"""
AXIUART Driver - Main Window

Main GUI application window for AXIUART communication software.
Provides comprehensive interface for UART-AXI4 protocol communication.
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import threading
import queue
import time
from datetime import datetime
from typing import Dict, Any, Optional, Callable

from core import COMManager, UARTProtocol, RegisterMap


class MainWindow:
    """
    Main GUI window for AXIUART Driver application.
    
    Features:
    - Connection management with COM port selection
    - Register access panel for read/write operations
    - Real-time status monitoring
    - Communication logging with timestamps
    """
    
    def __init__(self):
        """Initialize the main window and its components."""
        self.root = tk.Tk()
        self.root.title("AXIUART Driver - UART-AXI4 Communication Tool")
        self.root.geometry("900x700")
        self.root.minsize(800, 600)
        
        # Core communication objects
        self.com_manager: Optional[COMManager] = None
        self.uart_protocol: Optional[UARTProtocol] = None
        
        # Connection state
        self.is_connected = False
        self.current_port = ""
        self.current_baudrate = 115200
        
        # GUI update queue for thread-safe operations
        self.gui_queue = queue.Queue()
        
        # Statistics tracking
        self.stats = {
            'bytes_sent': 0,
            'bytes_received': 0,
            'commands_sent': 0,
            'errors': 0,
            'last_activity': None
        }
        
        # Setup GUI components
        self._create_widgets()
        self._setup_layout()
        self._bind_events()
        
        # Start GUI update timer
        self._start_gui_updater()
    
    def _create_widgets(self):
        """Create all GUI widgets."""
        # Main container with notebook for tabs
        self.notebook = ttk.Notebook(self.root)
        
        # Connection Management Tab
        self.conn_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.conn_frame, text="Connection")
        self._create_connection_widgets()
        
        # Register Access Tab
        self.reg_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.reg_frame, text="Registers")
        self._create_register_widgets()
        
        # Memory Access Tab
        self.memory_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.memory_frame, text="Memory")
        self._create_memory_widgets()
        
        # Status Monitoring Tab
        self.status_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.status_frame, text="Status")
        self._create_status_widgets()
        
        # Communication Log Tab
        self.log_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.log_frame, text="Logs")
        self._create_log_widgets()
    
    def _create_connection_widgets(self):
        """Create connection management widgets."""
        # Connection settings group
        conn_group = ttk.LabelFrame(self.conn_frame, text="Connection Settings", padding="10")
        
        # COM port selection
        ttk.Label(conn_group, text="COM Port:").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.port_var = tk.StringVar()
        self.port_combo = ttk.Combobox(conn_group, textvariable=self.port_var, width=15, state="readonly")
        self.port_combo.grid(row=0, column=1, padx=5, pady=5)
        
        # Refresh ports button
        self.refresh_btn = ttk.Button(conn_group, text="Refresh", command=self._refresh_ports)
        self.refresh_btn.grid(row=0, column=2, padx=5, pady=5)
        
        # Baudrate selection
        ttk.Label(conn_group, text="Baudrate:").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.baudrate_var = tk.StringVar(value="115200")
        self.baudrate_combo = ttk.Combobox(conn_group, textvariable=self.baudrate_var, width=15, 
                                          values=["9600", "19200", "38400", "57600", "115200", "230400"])
        self.baudrate_combo.grid(row=1, column=1, padx=5, pady=5)
        
        # Flow control settings
        ttk.Label(conn_group, text="Flow Control:").grid(row=2, column=0, sticky="w", padx=5, pady=5)
        self.flow_control_var = tk.BooleanVar(value=True)
        self.flow_control_check = ttk.Checkbutton(conn_group, text="RTS/CTS Hardware Flow Control", 
                                                 variable=self.flow_control_var)
        self.flow_control_check.grid(row=2, column=1, columnspan=2, sticky="w", padx=5, pady=5)
        
        # Connect/Disconnect button
        self.connect_btn = ttk.Button(conn_group, text="Connect", command=self._toggle_connection)
        self.connect_btn.grid(row=3, column=0, columnspan=3, pady=10)
        
        conn_group.pack(fill="x", padx=10, pady=10)
        
        # Connection status group
        status_group = ttk.LabelFrame(self.conn_frame, text="Connection Status", padding="10")
        
        # Status indicators
        self.status_label = ttk.Label(status_group, text="Status: Disconnected", font=("Arial", 10, "bold"))
        self.status_label.pack(anchor="w", pady=2)
        
        self.signal_status = ttk.Label(status_group, text="RTS: -, CTS: -, DSR: -, DTR: -")
        self.signal_status.pack(anchor="w", pady=2)
        
        status_group.pack(fill="x", padx=10, pady=5)
    
    def _create_register_widgets(self):
        """Create register access widgets."""
        # Register selection group
        reg_group = ttk.LabelFrame(self.reg_frame, text="Register Access", padding="10")
        
        # Register selection
        ttk.Label(reg_group, text="Register:").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.register_var = tk.StringVar()
        
        # Create register options from RegisterMap
        register_options = [
            ("CONTROL (0x1000)", "CONTROL"),
            ("STATUS (0x1004)", "STATUS"), 
            ("CONFIG (0x1008)", "CONFIG"),
            ("DEBUG (0x100C)", "DEBUG"),
            ("TX_COUNT (0x1010)", "TX_COUNT"),
            ("RX_COUNT (0x1014)", "RX_COUNT"),
            ("FIFO_STAT (0x1018)", "FIFO_STAT"),
            ("VERSION (0x101C)", "VERSION")
        ]
        
        self.register_combo = ttk.Combobox(reg_group, textvariable=self.register_var, width=25, state="readonly")
        self.register_combo['values'] = [opt[0] for opt in register_options]
        self.register_combo.grid(row=0, column=1, columnspan=2, padx=5, pady=5)
        
        # Data width selection
        ttk.Label(reg_group, text="Data Width:").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.data_width_var = tk.StringVar(value="32")
        self.data_width_combo = ttk.Combobox(reg_group, textvariable=self.data_width_var, width=10, 
                                           values=["8", "16", "32"], state="readonly")
        self.data_width_combo.grid(row=1, column=1, padx=5, pady=5)
        
        # Value input/display
        ttk.Label(reg_group, text="Value (Hex):").grid(row=2, column=0, sticky="w", padx=5, pady=5)
        self.value_var = tk.StringVar()
        self.value_entry = ttk.Entry(reg_group, textvariable=self.value_var, width=15)
        self.value_entry.grid(row=2, column=1, padx=5, pady=5)
        
        # Read/Write buttons
        self.read_btn = ttk.Button(reg_group, text="Read", command=self._read_register)
        self.read_btn.grid(row=3, column=0, padx=5, pady=10)
        
        self.write_btn = ttk.Button(reg_group, text="Write", command=self._write_register)
        self.write_btn.grid(row=3, column=1, padx=5, pady=10)
        
        # Clear button
        self.clear_btn = ttk.Button(reg_group, text="Clear", command=self._clear_value)
        self.clear_btn.grid(row=3, column=2, padx=5, pady=10)
        
        reg_group.pack(fill="x", padx=10, pady=10)
        
        # Quick access buttons for common operations
        quick_group = ttk.LabelFrame(self.reg_frame, text="Quick Access", padding="10")
        
        self.enable_bridge_btn = ttk.Button(quick_group, text="Enable Bridge", command=self._enable_bridge)
        self.enable_bridge_btn.pack(side="left", padx=5)
        
        self.disable_bridge_btn = ttk.Button(quick_group, text="Disable Bridge", command=self._disable_bridge)
        self.disable_bridge_btn.pack(side="left", padx=5)
        
        self.read_status_btn = ttk.Button(quick_group, text="Read Status", command=self._read_status)
        self.read_status_btn.pack(side="left", padx=5)
        
        self.read_version_btn = ttk.Button(quick_group, text="Read Version", command=self._read_version)
        self.read_version_btn.pack(side="left", padx=5)
        
        quick_group.pack(fill="x", padx=10, pady=5)
    
    def _create_memory_widgets(self):
        """Create memory access widgets for arbitrary address/data operations."""
        # Direct Memory Access group
        mem_group = ttk.LabelFrame(self.memory_frame, text="Direct Memory Access", padding="10")
        
        # Address input
        ttk.Label(mem_group, text="Address (Hex):").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.mem_address_var = tk.StringVar()
        self.mem_address_entry = ttk.Entry(mem_group, textvariable=self.mem_address_var, width=20)
        self.mem_address_entry.grid(row=0, column=1, padx=5, pady=5)
        ttk.Label(mem_group, text="(e.g., 1000, 0x1000)").grid(row=0, column=2, sticky="w", padx=5)
        
        # Data value input/display
        ttk.Label(mem_group, text="Data (Hex):").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.mem_data_var = tk.StringVar()
        self.mem_data_entry = ttk.Entry(mem_group, textvariable=self.mem_data_var, width=20)
        self.mem_data_entry.grid(row=1, column=1, padx=5, pady=5)
        ttk.Label(mem_group, text="(e.g., DEADBEEF, 0xFF)").grid(row=1, column=2, sticky="w", padx=5)
        
        # Data width selection
        ttk.Label(mem_group, text="Data Width:").grid(row=2, column=0, sticky="w", padx=5, pady=5)
        self.mem_width_var = tk.StringVar(value="32")
        self.mem_width_combo = ttk.Combobox(mem_group, textvariable=self.mem_width_var, width=10, 
                                           values=["8", "16", "32"], state="readonly")
        self.mem_width_combo.grid(row=2, column=1, sticky="w", padx=5, pady=5)
        
        # Read/Write buttons
        button_frame = ttk.Frame(mem_group)
        button_frame.grid(row=3, column=0, columnspan=3, pady=10)
        
        self.mem_read_btn = ttk.Button(button_frame, text="Read", command=self._read_memory)
        self.mem_read_btn.pack(side="left", padx=5)
        
        self.mem_write_btn = ttk.Button(button_frame, text="Write", command=self._write_memory)
        self.mem_write_btn.pack(side="left", padx=5)
        
        self.mem_read_verify_btn = ttk.Button(button_frame, text="Write & Verify", command=self._write_verify_memory)
        self.mem_read_verify_btn.pack(side="left", padx=5)
        
        self.mem_clear_btn = ttk.Button(button_frame, text="Clear", command=self._clear_memory_fields)
        self.mem_clear_btn.pack(side="left", padx=5)
        
        mem_group.pack(fill="x", padx=10, pady=10)
        
        # Bulk Memory Operations group
        bulk_group = ttk.LabelFrame(self.memory_frame, text="Bulk Memory Operations", padding="10")
        
        # Start address
        ttk.Label(bulk_group, text="Start Address:").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.bulk_start_var = tk.StringVar()
        self.bulk_start_entry = ttk.Entry(bulk_group, textvariable=self.bulk_start_var, width=15)
        self.bulk_start_entry.grid(row=0, column=1, padx=5, pady=5)
        
        # Count
        ttk.Label(bulk_group, text="Count:").grid(row=0, column=2, sticky="w", padx=5, pady=5)
        self.bulk_count_var = tk.StringVar(value="4")
        self.bulk_count_entry = ttk.Entry(bulk_group, textvariable=self.bulk_count_var, width=10)
        self.bulk_count_entry.grid(row=0, column=3, padx=5, pady=5)
        
        # Fill pattern
        ttk.Label(bulk_group, text="Fill Pattern:").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.bulk_pattern_var = tk.StringVar(value="00000000")
        self.bulk_pattern_entry = ttk.Entry(bulk_group, textvariable=self.bulk_pattern_var, width=15)
        self.bulk_pattern_entry.grid(row=1, column=1, padx=5, pady=5)
        
        # Bulk operation buttons
        bulk_button_frame = ttk.Frame(bulk_group)
        bulk_button_frame.grid(row=2, column=0, columnspan=4, pady=10)
        
        self.bulk_read_btn = ttk.Button(bulk_button_frame, text="Bulk Read", command=self._bulk_read_memory)
        self.bulk_read_btn.pack(side="left", padx=5)
        
        self.bulk_fill_btn = ttk.Button(bulk_button_frame, text="Fill Memory", command=self._bulk_fill_memory)
        self.bulk_fill_btn.pack(side="left", padx=5)
        
        self.bulk_test_btn = ttk.Button(bulk_button_frame, text="Memory Test", command=self._memory_test)
        self.bulk_test_btn.pack(side="left", padx=5)
        
        bulk_group.pack(fill="x", padx=10, pady=10)
        
        # Memory dump display
        dump_group = ttk.LabelFrame(self.memory_frame, text="Memory Dump", padding="10")
        
        # Text widget with scrollbar for memory dump
        dump_frame = ttk.Frame(dump_group)
        dump_frame.pack(fill="both", expand=True)
        
        self.memory_dump_text = scrolledtext.ScrolledText(dump_frame, height=15, width=80, 
                                                         font=("Courier", 9), state="disabled")
        self.memory_dump_text.pack(fill="both", expand=True)
        
        # Dump control buttons
        dump_control_frame = ttk.Frame(dump_group)
        dump_control_frame.pack(fill="x", pady=5)
        
        self.dump_clear_btn = ttk.Button(dump_control_frame, text="Clear Dump", command=self._clear_memory_dump)
        self.dump_clear_btn.pack(side="left", padx=5)
        
        self.dump_save_btn = ttk.Button(dump_control_frame, text="Save Dump", command=self._save_memory_dump)
        self.dump_save_btn.pack(side="left", padx=5)
        
        # Auto-format checkbox
        self.dump_format_var = tk.BooleanVar(value=True)
        self.dump_format_check = ttk.Checkbutton(dump_control_frame, text="Format as Hex Dump", 
                                                variable=self.dump_format_var)
        self.dump_format_check.pack(side="left", padx=10)
        
        dump_group.pack(fill="both", expand=True, padx=10, pady=5)
    
    def _create_status_widgets(self):
        """Create status monitoring widgets."""
        # Statistics group
        stats_group = ttk.LabelFrame(self.status_frame, text="Communication Statistics", padding="10")
        
        self.stats_text = tk.Text(stats_group, height=8, width=50, state="disabled")
        self.stats_text.pack(fill="both", expand=True)
        
        stats_group.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Control buttons
        control_group = ttk.Frame(self.status_frame)
        
        self.reset_stats_btn = ttk.Button(control_group, text="Reset Statistics", command=self._reset_statistics)
        self.reset_stats_btn.pack(side="left", padx=5)
        
        self.update_stats_btn = ttk.Button(control_group, text="Update Now", command=self._update_statistics)
        self.update_stats_btn.pack(side="left", padx=5)
        
        control_group.pack(pady=5)
    
    def _create_log_widgets(self):
        """Create communication log widgets."""
        # Log display
        log_group = ttk.LabelFrame(self.log_frame, text="Communication Log", padding="10")
        
        self.log_text = scrolledtext.ScrolledText(log_group, height=20, width=80, state="disabled")
        self.log_text.pack(fill="both", expand=True)
        
        log_group.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Log controls
        control_group = ttk.Frame(self.log_frame)
        
        self.clear_log_btn = ttk.Button(control_group, text="Clear Log", command=self._clear_log)
        self.clear_log_btn.pack(side="left", padx=5)
        
        self.save_log_btn = ttk.Button(control_group, text="Save Log", command=self._save_log)
        self.save_log_btn.pack(side="left", padx=5)
        
        # Auto-scroll checkbox
        self.auto_scroll_var = tk.BooleanVar(value=True)
        self.auto_scroll_check = ttk.Checkbutton(control_group, text="Auto Scroll", variable=self.auto_scroll_var)
        self.auto_scroll_check.pack(side="left", padx=10)
        
        control_group.pack(pady=5)
    
    def _setup_layout(self):
        """Setup the main layout."""
        self.notebook.pack(fill="both", expand=True, padx=5, pady=5)
    
    def _bind_events(self):
        """Bind event handlers."""
        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)
        
        # Enable/disable register controls based on connection status
        self._update_widget_states()
    
    def _start_gui_updater(self):
        """Start the GUI update timer."""
        self._process_gui_queue()
        self._update_connection_status()
        self.root.after(100, self._start_gui_updater)  # Update every 100ms
    
    def _process_gui_queue(self):
        """Process GUI update messages from background threads."""
        try:
            while True:
                message = self.gui_queue.get_nowait()
                if message['type'] == 'log':
                    self._add_log_entry(message['text'])
                elif message['type'] == 'status':
                    self._update_status_display(message['data'])
        except queue.Empty:
            pass
    
    def _refresh_ports(self):
        """Refresh available COM ports."""
        if self.com_manager is None:
            self.com_manager = COMManager()
        
        ports = self.com_manager.list_ports()
        self.port_combo['values'] = [f"{port.device} - {port.description}" for port in ports]
        if ports:
            self.port_combo.current(0)
    
    def _toggle_connection(self):
        """Toggle connection state."""
        if not self.is_connected:
            self._connect()
        else:
            self._disconnect()
    
    def _connect(self):
        """Establish connection to selected COM port."""
        try:
            if not self.port_var.get():
                messagebox.showerror("Error", "Please select a COM port")
                return
            
            # Extract port name from selection
            port_name = self.port_var.get().split(" - ")[0]
            baudrate = int(self.baudrate_var.get())
            
            # Initialize COM manager if needed
            if self.com_manager is None:
                self.com_manager = COMManager()
            
            # Connect
            success = self.com_manager.connect(port_name, baudrate, 
                                             flow_control=self.flow_control_var.get())
            
            if success:
                self.uart_protocol = UARTProtocol(self.com_manager)
                self.is_connected = True
                self.current_port = port_name
                self.current_baudrate = baudrate
                
                self.connect_btn.config(text="Disconnect")
                self._update_widget_states()
                self._add_log_entry(f"Connected to {port_name} at {baudrate} baud")
                
                messagebox.showinfo("Success", f"Connected to {port_name}")
            else:
                messagebox.showerror("Error", f"Failed to connect to {port_name}")
                
        except Exception as e:
            messagebox.showerror("Connection Error", f"Failed to connect: {str(e)}")
            self._add_log_entry(f"Connection failed: {str(e)}")
    
    def _disconnect(self):
        """Disconnect from COM port."""
        try:
            if self.com_manager:
                self.com_manager.disconnect()
            
            self.is_connected = False
            self.uart_protocol = None
            
            self.connect_btn.config(text="Connect")
            self._update_widget_states()
            self._add_log_entry(f"Disconnected from {self.current_port}")
            
            messagebox.showinfo("Disconnected", "Connection closed")
            
        except Exception as e:
            messagebox.showerror("Disconnect Error", f"Failed to disconnect: {str(e)}")
    
    def _update_widget_states(self):
        """Update widget enabled/disabled states based on connection."""
        # Connection controls
        state = "disabled" if self.is_connected else "normal"
        self.port_combo.config(state=state)
        self.baudrate_combo.config(state=state)
        self.refresh_btn.config(state=state)
        self.flow_control_check.config(state=state)
        
        # Register controls
        reg_state = "normal" if self.is_connected else "disabled"
        self.register_combo.config(state=reg_state)
        self.data_width_combo.config(state=reg_state)
        self.value_entry.config(state=reg_state)
        self.read_btn.config(state=reg_state)
        self.write_btn.config(state=reg_state)
        self.clear_btn.config(state=reg_state)
        
        # Quick access buttons
        self.enable_bridge_btn.config(state=reg_state)
        self.disable_bridge_btn.config(state=reg_state)
        self.read_status_btn.config(state=reg_state)
        self.read_version_btn.config(state=reg_state)
        
        # Memory access controls
        self.mem_address_entry.config(state=reg_state)
        self.mem_data_entry.config(state=reg_state)
        self.mem_width_combo.config(state=reg_state)
        self.mem_read_btn.config(state=reg_state)
        self.mem_write_btn.config(state=reg_state)
        self.mem_read_verify_btn.config(state=reg_state)
        self.mem_clear_btn.config(state=reg_state)
        
        # Bulk operation controls
        self.bulk_start_entry.config(state=reg_state)
        self.bulk_count_entry.config(state=reg_state)
        self.bulk_pattern_entry.config(state=reg_state)
        self.bulk_read_btn.config(state=reg_state)
        self.bulk_fill_btn.config(state=reg_state)
        self.bulk_test_btn.config(state=reg_state)
    
    def _update_connection_status(self):
        """Update connection status display."""
        if self.is_connected and self.com_manager:
            status_text = f"Status: Connected to {self.current_port} ({self.current_baudrate} baud)"
            self.status_label.config(text=status_text, foreground="green")
            
            # Update signal status if available
            try:
                signals = self.com_manager.get_signals()
                signal_text = f"RTS: {'High' if signals.get('rts', False) else 'Low'}, " \
                             f"CTS: {'High' if signals.get('cts', False) else 'Low'}, " \
                             f"DSR: {'High' if signals.get('dsr', False) else 'Low'}, " \
                             f"DTR: {'High' if signals.get('dtr', False) else 'Low'}"
                self.signal_status.config(text=signal_text)
            except:
                self.signal_status.config(text="Signal status unavailable")
        else:
            self.status_label.config(text="Status: Disconnected", foreground="red")
            self.signal_status.config(text="RTS: -, CTS: -, DSR: -, DTR: -")
    
    def _add_log_entry(self, text: str):
        """Add entry to communication log."""
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        log_entry = f"[{timestamp}] {text}\n"
        
        self.log_text.config(state="normal")
        self.log_text.insert(tk.END, log_entry)
        
        if self.auto_scroll_var.get():
            self.log_text.see(tk.END)
        
        self.log_text.config(state="disabled")
    
    def _read_register(self):
        """Read from selected register."""
        if not self._validate_register_selection():
            return
        
        try:
            register_name = self._get_selected_register_name()
            register_addr = getattr(RegisterMap, register_name)
            data_width = int(self.data_width_var.get())
            
            self._add_log_entry(f"Reading {register_name} (0x{register_addr:04X}), width: {data_width}")
            
            # Perform read operation
            value = self.uart_protocol.register_read(register_addr, data_width)
            
            # Display result
            self.value_var.set(f"{value:0{data_width//4}X}")
            self._add_log_entry(f"Read result: 0x{value:0{data_width//4}X}")
            
            # Update statistics
            self.stats['commands_sent'] += 1
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Read failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Read Error", error_msg)
            self.stats['errors'] += 1
    
    def _write_register(self):
        """Write to selected register."""
        if not self._validate_register_selection():
            return
        
        try:
            register_name = self._get_selected_register_name()
            register_addr = getattr(RegisterMap, register_name)
            data_width = int(self.data_width_var.get())
            
            # Parse value
            value_str = self.value_var.get().strip()
            if not value_str:
                messagebox.showerror("Error", "Please enter a value to write")
                return
            
            # Remove 0x prefix if present
            if value_str.lower().startswith('0x'):
                value_str = value_str[2:]
            
            value = int(value_str, 16)
            
            # Validate value range
            max_value = (1 << data_width) - 1
            if value > max_value:
                messagebox.showerror("Error", f"Value too large for {data_width}-bit register")
                return
            
            self._add_log_entry(f"Writing {register_name} (0x{register_addr:04X}) = 0x{value:0{data_width//4}X}")
            
            # Perform write operation
            self.uart_protocol.register_write(register_addr, value, data_width)
            self._add_log_entry(f"Write completed successfully")
            
            # Update statistics
            self.stats['commands_sent'] += 1
            self.stats['last_activity'] = datetime.now()
            
        except ValueError:
            error_msg = "Invalid hexadecimal value"
            messagebox.showerror("Input Error", error_msg)
            self._add_log_entry(error_msg)
        except Exception as e:
            error_msg = f"Write failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Write Error", error_msg)
            self.stats['errors'] += 1
    
    def _validate_register_selection(self) -> bool:
        """Validate that a register is selected."""
        if not self.is_connected:
            messagebox.showerror("Error", "Not connected to COM port")
            return False
        
        if not self.register_var.get():
            messagebox.showerror("Error", "Please select a register")
            return False
        
        return True
    
    def _get_selected_register_name(self) -> str:
        """Get the register name from selection."""
        selection = self.register_var.get()
        # Extract register name from "NAME (0xADDR)" format
        return selection.split(" (")[0]
    
    def _clear_value(self):
        """Clear the value entry field."""
        self.value_var.set("")
    
    def _enable_bridge(self):
        """Quick function to enable the bridge."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            self.uart_protocol.register_write(RegisterMap.CONTROL, RegisterMap.CONTROL_BRIDGE_ENABLE)
            self._add_log_entry("Bridge enabled")
            messagebox.showinfo("Success", "Bridge enabled")
            
        except Exception as e:
            error_msg = f"Failed to enable bridge: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Error", error_msg)
    
    def _disable_bridge(self):
        """Quick function to disable the bridge."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            self.uart_protocol.register_write(RegisterMap.CONTROL, 0)
            self._add_log_entry("Bridge disabled")
            messagebox.showinfo("Success", "Bridge disabled")
            
        except Exception as e:
            error_msg = f"Failed to disable bridge: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Error", error_msg)
    
    def _read_status(self):
        """Quick function to read status register."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            status = self.uart_protocol.register_read(RegisterMap.STATUS)
            self._add_log_entry(f"Status register: 0x{status:08X}")
            
            # Decode status bits
            status_text = f"Status: 0x{status:08X}\n"
            if status & RegisterMap.STATUS_BRIDGE_ACTIVE:
                status_text += "- Bridge Active\n"
            if status & RegisterMap.STATUS_TX_FIFO_FULL:
                status_text += "- TX FIFO Full\n"
            if status & RegisterMap.STATUS_RX_FIFO_EMPTY:
                status_text += "- RX FIFO Empty\n"
            
            messagebox.showinfo("Status Register", status_text)
            
        except Exception as e:
            error_msg = f"Failed to read status: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Error", error_msg)
    
    def _read_version(self):
        """Quick function to read version register."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            version = self.uart_protocol.register_read(RegisterMap.VERSION)
            major = (version >> 24) & 0xFF
            minor = (version >> 16) & 0xFF
            patch = (version >> 8) & 0xFF
            build = version & 0xFF
            
            version_text = f"Version: {major}.{minor}.{patch}.{build}"
            self._add_log_entry(version_text)
            messagebox.showinfo("Version", version_text)
            
        except Exception as e:
            error_msg = f"Failed to read version: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Error", error_msg)
    
    def _update_statistics(self):
        """Update statistics display."""
        if not self.uart_protocol:
            return
        
        stats = self.uart_protocol.get_statistics()
        self.stats.update(stats)
        
        stats_text = f"""Communication Statistics:

Commands Sent: {self.stats.get('commands_sent', 0)}
Successful Responses: {self.stats.get('successful_responses', 0)}
Failed Commands: {self.stats.get('failed_commands', 0)}
CRC Errors: {self.stats.get('crc_errors', 0)}
Timeout Errors: {self.stats.get('timeout_errors', 0)}
Retry Count: {self.stats.get('retry_count', 0)}

Bytes Sent: {self.stats.get('bytes_sent', 0)}
Bytes Received: {self.stats.get('bytes_received', 0)}

Last Activity: {self.stats.get('last_activity', 'Never')}
"""
        
        self.stats_text.config(state="normal")
        self.stats_text.delete("1.0", tk.END)
        self.stats_text.insert("1.0", stats_text)
        self.stats_text.config(state="disabled")
    
    def _reset_statistics(self):
        """Reset communication statistics."""
        if self.uart_protocol:
            self.uart_protocol.reset_statistics()
        
        self.stats = {
            'bytes_sent': 0,
            'bytes_received': 0,
            'commands_sent': 0,
            'errors': 0,
            'last_activity': None
        }
        
        self._update_statistics()
        self._add_log_entry("Statistics reset")
    
    def _clear_log(self):
        """Clear the communication log."""
        self.log_text.config(state="normal")
        self.log_text.delete("1.0", tk.END)
        self.log_text.config(state="disabled")
        self._add_log_entry("Log cleared")
    
    def _save_log(self):
        """Save communication log to file."""
        from tkinter import filedialog
        
        filename = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            title="Save Communication Log"
        )
        
        if filename:
            try:
                log_content = self.log_text.get("1.0", tk.END)
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(log_content)
                self._add_log_entry(f"Log saved to {filename}")
                messagebox.showinfo("Success", f"Log saved to {filename}")
            except Exception as e:
                error_msg = f"Failed to save log: {str(e)}"
                self._add_log_entry(error_msg)
                messagebox.showerror("Save Error", error_msg)
    
    # Memory Access Methods
    def _parse_hex_value(self, hex_str: str) -> int:
        """Parse hexadecimal string to integer."""
        hex_str = hex_str.strip()
        if not hex_str:
            raise ValueError("Empty value")
        
        # Remove 0x prefix if present
        if hex_str.lower().startswith('0x'):
            hex_str = hex_str[2:]
        
        return int(hex_str, 16)
    
    def _format_hex_value(self, value: int, width: int) -> str:
        """Format integer as hexadecimal string."""
        hex_digits = width // 4
        return f"{value:0{hex_digits}X}"
    
    def _validate_memory_inputs(self) -> tuple[int, int, int]:
        """Validate and parse memory access inputs."""
        if not self.is_connected:
            raise ValueError("Not connected to COM port")
        
        # Parse address
        try:
            address = self._parse_hex_value(self.mem_address_var.get())
        except ValueError:
            raise ValueError("Invalid address format")
        
        # Parse data width
        width = int(self.mem_width_var.get())
        
        # Parse data (for write operations)
        data_str = self.mem_data_var.get().strip()
        if data_str:
            try:
                data = self._parse_hex_value(data_str)
                max_value = (1 << width) - 1
                if data > max_value:
                    raise ValueError(f"Data value too large for {width}-bit width")
            except ValueError as e:
                if "too large" in str(e):
                    raise e
                raise ValueError("Invalid data format")
        else:
            data = 0
        
        return address, data, width
    
    def _read_memory(self):
        """Read from arbitrary memory address."""
        try:
            address, _, width = self._validate_memory_inputs()
            
            self._add_log_entry(f"Reading memory address 0x{address:08X}, width: {width}")
            
            # Perform read operation
            value = self.uart_protocol.register_read(address, width)
            
            # Display result
            self.mem_data_var.set(self._format_hex_value(value, width))
            self._add_log_entry(f"Read result: 0x{value:0{width//4}X}")
            
            # Add to memory dump
            self._add_to_memory_dump(address, value, width, "READ")
            
            # Update statistics
            self.stats['commands_sent'] += 1
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Memory read failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Read Error", error_msg)
            self.stats['errors'] += 1
    
    def _write_memory(self):
        """Write to arbitrary memory address."""
        try:
            address, data, width = self._validate_memory_inputs()
            
            if not self.mem_data_var.get().strip():
                messagebox.showerror("Error", "Please enter data value to write")
                return
            
            self._add_log_entry(f"Writing memory address 0x{address:08X} = 0x{data:0{width//4}X}")
            
            # Perform write operation
            self.uart_protocol.register_write(address, data, width)
            self._add_log_entry(f"Write completed successfully")
            
            # Add to memory dump
            self._add_to_memory_dump(address, data, width, "WRITE")
            
            # Update statistics
            self.stats['commands_sent'] += 1
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Memory write failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Write Error", error_msg)
            self.stats['errors'] += 1
    
    def _write_verify_memory(self):
        """Write to memory and verify by reading back."""
        try:
            address, data, width = self._validate_memory_inputs()
            
            if not self.mem_data_var.get().strip():
                messagebox.showerror("Error", "Please enter data value to write")
                return
            
            self._add_log_entry(f"Write & Verify: address 0x{address:08X} = 0x{data:0{width//4}X}")
            
            # Perform write operation
            self.uart_protocol.register_write(address, data, width)
            self._add_log_entry(f"Write completed, verifying...")
            
            # Read back for verification
            read_value = self.uart_protocol.register_read(address, width)
            
            if read_value == data:
                self._add_log_entry(f"✓ Verification passed: 0x{read_value:0{width//4}X}")
                self._add_to_memory_dump(address, data, width, "WRITE+VERIFY ✓")
                messagebox.showinfo("Success", "Write & Verify completed successfully")
            else:
                error_msg = f"✗ Verification failed: wrote 0x{data:0{width//4}X}, read 0x{read_value:0{width//4}X}"
                self._add_log_entry(error_msg)
                self._add_to_memory_dump(address, read_value, width, "WRITE+VERIFY ✗")
                messagebox.showerror("Verification Failed", error_msg)
                self.stats['errors'] += 1
            
            # Update display with read value
            self.mem_data_var.set(self._format_hex_value(read_value, width))
            
            # Update statistics
            self.stats['commands_sent'] += 2  # Write + Read
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Write & Verify failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Write & Verify Error", error_msg)
            self.stats['errors'] += 1
    
    def _clear_memory_fields(self):
        """Clear memory access input fields."""
        self.mem_address_var.set("")
        self.mem_data_var.set("")
    
    def _bulk_read_memory(self):
        """Read multiple consecutive memory locations."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            # Parse inputs
            start_addr = self._parse_hex_value(self.bulk_start_var.get())
            count = int(self.bulk_count_var.get())
            width = int(self.mem_width_var.get())
            
            if count <= 0 or count > 256:
                messagebox.showerror("Error", "Count must be between 1 and 256")
                return
            
            self._add_log_entry(f"Bulk reading {count} locations from 0x{start_addr:08X}")
            
            # Perform bulk read
            results = []
            for i in range(count):
                addr = start_addr + (i * (width // 8))
                try:
                    value = self.uart_protocol.register_read(addr, width)
                    results.append((addr, value))
                    self._add_to_memory_dump(addr, value, width, "BULK_READ")
                except Exception as e:
                    self._add_log_entry(f"Error reading 0x{addr:08X}: {str(e)}")
                    results.append((addr, None))
            
            # Display results summary
            success_count = len([r for r in results if r[1] is not None])
            self._add_log_entry(f"Bulk read completed: {success_count}/{count} successful")
            
            if success_count < count:
                messagebox.showwarning("Partial Success", f"Only {success_count}/{count} reads successful")
            else:
                messagebox.showinfo("Success", f"All {count} reads completed successfully")
            
            # Update statistics
            self.stats['commands_sent'] += count
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Bulk read failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Bulk Read Error", error_msg)
            self.stats['errors'] += 1
    
    def _bulk_fill_memory(self):
        """Fill multiple memory locations with a pattern."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            # Parse inputs
            start_addr = self._parse_hex_value(self.bulk_start_var.get())
            count = int(self.bulk_count_var.get())
            pattern = self._parse_hex_value(self.bulk_pattern_var.get())
            width = int(self.mem_width_var.get())
            
            if count <= 0 or count > 256:
                messagebox.showerror("Error", "Count must be between 1 and 256")
                return
            
            # Confirm dangerous operation
            if not messagebox.askyesno("Confirm Fill", 
                                     f"Fill {count} locations from 0x{start_addr:08X} with 0x{pattern:0{width//4}X}?"):
                return
            
            self._add_log_entry(f"Bulk filling {count} locations from 0x{start_addr:08X} with 0x{pattern:0{width//4}X}")
            
            # Perform bulk write
            success_count = 0
            for i in range(count):
                addr = start_addr + (i * (width // 8))
                try:
                    self.uart_protocol.register_write(addr, pattern, width)
                    self._add_to_memory_dump(addr, pattern, width, "BULK_FILL")
                    success_count += 1
                except Exception as e:
                    self._add_log_entry(f"Error writing 0x{addr:08X}: {str(e)}")
                    self.stats['errors'] += 1
            
            self._add_log_entry(f"Bulk fill completed: {success_count}/{count} successful")
            
            if success_count < count:
                messagebox.showwarning("Partial Success", f"Only {success_count}/{count} writes successful")
            else:
                messagebox.showinfo("Success", f"All {count} writes completed successfully")
            
            # Update statistics
            self.stats['commands_sent'] += count
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Bulk fill failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Bulk Fill Error", error_msg)
            self.stats['errors'] += 1
    
    def _memory_test(self):
        """Perform basic memory test (write patterns and verify)."""
        try:
            if not self.is_connected:
                messagebox.showerror("Error", "Not connected")
                return
            
            # Parse inputs
            start_addr = self._parse_hex_value(self.bulk_start_var.get())
            count = int(self.bulk_count_var.get())
            width = int(self.mem_width_var.get())
            
            if count <= 0 or count > 64:
                messagebox.showerror("Error", "Memory test count must be between 1 and 64")
                return
            
            # Confirm test operation
            if not messagebox.askyesno("Confirm Memory Test", 
                                     f"Test {count} locations from 0x{start_addr:08X}?\nThis will overwrite existing data!"):
                return
            
            self._add_log_entry(f"Starting memory test: {count} locations from 0x{start_addr:08X}")
            
            test_patterns = [0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA]
            total_tests = 0
            passed_tests = 0
            
            for pattern_idx, pattern in enumerate(test_patterns):
                # Adjust pattern for width
                if width == 8:
                    pattern &= 0xFF
                elif width == 16:
                    pattern &= 0xFFFF
                elif width == 32:
                    pattern &= 0xFFFFFFFF
                
                self._add_log_entry(f"Testing pattern {pattern_idx+1}/4: 0x{pattern:0{width//4}X}")
                
                for i in range(count):
                    addr = start_addr + (i * (width // 8))
                    try:
                        # Write pattern
                        self.uart_protocol.register_write(addr, pattern, width)
                        # Read back and verify
                        read_value = self.uart_protocol.register_read(addr, width)
                        
                        total_tests += 1
                        if read_value == pattern:
                            passed_tests += 1
                        else:
                            self._add_log_entry(f"FAIL: 0x{addr:08X} wrote 0x{pattern:0{width//4}X}, read 0x{read_value:0{width//4}X}")
                            self.stats['errors'] += 1
                        
                        self._add_to_memory_dump(addr, read_value, width, f"TEST_{pattern_idx+1}")
                        
                    except Exception as e:
                        self._add_log_entry(f"ERROR: 0x{addr:08X}: {str(e)}")
                        total_tests += 1
                        self.stats['errors'] += 1
            
            # Test summary
            success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
            summary = f"Memory test completed: {passed_tests}/{total_tests} passed ({success_rate:.1f}%)"
            self._add_log_entry(summary)
            
            if passed_tests == total_tests:
                messagebox.showinfo("Test Success", summary + "\nMemory test PASSED")
            else:
                messagebox.showwarning("Test Failed", summary + "\nMemory test FAILED")
            
            # Update statistics
            self.stats['commands_sent'] += total_tests * 2  # Write + Read for each test
            self.stats['last_activity'] = datetime.now()
            
        except Exception as e:
            error_msg = f"Memory test failed: {str(e)}"
            self._add_log_entry(error_msg)
            messagebox.showerror("Memory Test Error", error_msg)
            self.stats['errors'] += 1
    
    def _add_to_memory_dump(self, address: int, data: int, width: int, operation: str):
        """Add entry to memory dump display."""
        timestamp = datetime.now().strftime("%H:%M:%S")
        
        if self.dump_format_var.get():
            # Formatted hex dump style
            entry = f"[{timestamp}] {operation:12} 0x{address:08X}: 0x{data:0{width//4}X}"
            if width == 32:
                # Add ASCII representation for 32-bit values
                ascii_chars = ""
                for i in range(4):
                    byte_val = (data >> (i * 8)) & 0xFF
                    ascii_chars += chr(byte_val) if 32 <= byte_val <= 126 else '.'
                entry += f"  |{ascii_chars}|"
        else:
            # Simple format
            entry = f"[{timestamp}] {operation} 0x{address:08X} = 0x{data:0{width//4}X}"
        
        entry += "\n"
        
        self.memory_dump_text.config(state="normal")
        self.memory_dump_text.insert(tk.END, entry)
        self.memory_dump_text.see(tk.END)
        self.memory_dump_text.config(state="disabled")
    
    def _clear_memory_dump(self):
        """Clear memory dump display."""
        self.memory_dump_text.config(state="normal")
        self.memory_dump_text.delete("1.0", tk.END)
        self.memory_dump_text.config(state="disabled")
        self._add_log_entry("Memory dump cleared")
    
    def _save_memory_dump(self):
        """Save memory dump to file."""
        from tkinter import filedialog
        
        filename = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("Memory dump", "*.memdump"), ("All files", "*.*")],
            title="Save Memory Dump"
        )
        
        if filename:
            try:
                dump_content = self.memory_dump_text.get("1.0", tk.END)
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(dump_content)
                self._add_log_entry(f"Memory dump saved to {filename}")
                messagebox.showinfo("Success", f"Memory dump saved to {filename}")
            except Exception as e:
                error_msg = f"Failed to save memory dump: {str(e)}"
                self._add_log_entry(error_msg)
                messagebox.showerror("Save Error", error_msg)
    
    def _on_closing(self):
        """Handle window closing event."""
        if self.is_connected:
            if messagebox.askyesno("Confirm Exit", "Still connected. Disconnect and exit?"):
                self._disconnect()
                self.root.destroy()
        else:
            self.root.destroy()
    
    def run(self):
        """Start the GUI application."""
        # Initialize port list
        self._refresh_ports()
        
        # Start the main loop
        self.root.mainloop()


def main():
    """Main entry point for GUI application."""
    app = MainWindow()
    app.run()


if __name__ == "__main__":
    main()