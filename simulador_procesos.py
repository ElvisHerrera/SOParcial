
# -*- coding: utf-8 -*-
"""
Simulador — Estados de los Procesos
"""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum, auto
from typing import Optional, Deque, List, Dict, Tuple
from collections import deque, defaultdict
import random

from PySide6.QtCore import QTimer, QSize
from PySide6.QtGui import QColor, QBrush
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QPushButton, QTableWidget, QTableWidgetItem,
    QHeaderView, QVBoxLayout, QHBoxLayout, QGroupBox, QMessageBox, QComboBox, QCheckBox, QSpinBox,
    QSizePolicy, QScrollArea, QToolButton, QStyle, QInputDialog
)

# 50 aplicaciones/servicios para demo y nombres automáticos
APPS_50 = [
    "Word","Excel","PowerPoint","Outlook","OneNote",
    "Teams","Zoom","Slack","Discord","Skype",
    "Chrome","Edge","Firefox","Opera","Brave",
    "Notepad","Bloc de notas","Paint","Calculadora","VLC",
    "Spotify","Steam","Epic Games","Adobe Acrobat","Photoshop",
    "Illustrator","Lightroom","WhatsApp Desktop","Telegram","Dropbox",
    "OneDrive","7-Zip","WinRAR","OBS Studio","Visual Studio",
    "VS Code","Git","Python","Node.js","Java",
    "MySQL","PostgreSQL","SQL Server","Docker","nginx",
    "Apache","VirtualBox","VMware Workstation","Windows Update","Defender"
]

# ---------------- Enumerados y etiquetas ----------------
class ProcessState(Enum):
    NEW = auto()
    READY = auto()
    RUNNING = auto()
    BLOCKED = auto()
    PAUSED = auto()
    FINISHED = auto()
    ZOMBIE = auto()

class BlockReason(Enum):
    IO = auto()
    DEPENDENCY = auto()
    PAUSED = auto()

class Priority(Enum):
    HIGH = auto()
    MEDIUM = auto()
    LOW = auto()

PRIO_LABEL = {Priority.HIGH:"Alta", Priority.MEDIUM:"Media", Priority.LOW:"Baja"}
PRIO_QUANTUM = {Priority.HIGH:4, Priority.MEDIUM:3, Priority.LOW:2}  # ticks seguidos por proceso

STATE_COLORS = {
    ProcessState.NEW: QColor(66,135,245),
    ProcessState.READY: QColor(245,211,66),
    ProcessState.RUNNING: QColor(82,196,26),
    ProcessState.BLOCKED: QColor(255,159,28),
    ProcessState.PAUSED: QColor(128,90,213),
    ProcessState.FINISHED: QColor(120,120,120),
    ProcessState.ZOMBIE: QColor(220,38,38),
}

STATE_LABEL_ES = {
    ProcessState.RUNNING: "Ejecución",
    ProcessState.BLOCKED: "Bloqueado",
    ProcessState.PAUSED: "Pausado",
    ProcessState.FINISHED: "Finalizado",
}
REASON_LABEL_ES = {
    BlockReason.PAUSED: "Pausado",
    BlockReason.DEPENDENCY: "Dependencia",
    BlockReason.IO: "I/O",
}

# ---------------- Modelo de proceso ----------------
@dataclass
class Process:
    pid: int
    name: str
    arrival_time: int
    burst_time: int
    remaining_time: int
    state: ProcessState = ProcessState.NEW
    block_reason: Optional[BlockReason] = None
    waiting_for_pid: Optional[int] = None
    io_remaining: int = 0
    priority: Priority = Priority.MEDIUM
    # Consumos simulados
    cpu_base: float = 0.0
    mem_base: int = 0
    disk_base: float = 0.0
    cpu_usage: float = 0.0
    mem_usage: int = 0
    disk_usage: float = 0.0

    def set_state(self, st: ProcessState):
        self.state = st

# ---------------- Planificador ----------------
class Scheduler:
    WRR_WEIGHTS = {Priority.HIGH:2, Priority.MEDIUM:2, Priority.LOW:1}  # por CLASE
    PRIO_CYCLE = [Priority.HIGH, Priority.MEDIUM, Priority.LOW]

    def __init__(self, simulate_zombie: bool=False, repeat_mode: bool=True):
        self.time: int = 0
        self.next_pid: int = 1
        self.simulate_zombie = simulate_zombie
        self.repeat_mode = repeat_mode

        self.new: List[Process] = []
        self.ready: Deque[Process] = deque()
        self.blocked: List[Process] = []
        self.finished: List[Process] = []
        self.zombies: List[Process] = []
        self.running: Optional[Process] = None

        self._rnd = random.Random()
        self.mailboxes: Dict[int, List[Tuple[int,str,int]]] = defaultdict(list)
        self._spawned_when_empty = False
        self._quantum_used: int = 0

        # WRR
        self._wrr_idx: int = 0
        self._wrr_budget: int = self.WRR_WEIGHTS[self.PRIO_CYCLE[self._wrr_idx]]

    # ---- utilidades nombres/recursos ----
    def _all_processes(self) -> List[Process]:
        out = []
        if self.running: out.append(self.running)
        out += list(self.ready) + self.blocked + self.finished + self.zombies + self.new
        return out

    def _existing_names(self) -> List[str]:
        return [p.name for p in self._all_processes()]

    def unique_name(self, base: str) -> str:
        names = set(self._existing_names())
        if base not in names: return base
        i = 1
        while True:
            cand = f"{base} ({i})"
            if cand not in names: return cand
            i += 1

    def _random_app_name(self) -> str:
        return self.unique_name(self._rnd.choice(APPS_50))

    def _init_resources(self) -> Tuple[float,int,float]:
        cpu = self._rnd.uniform(5, 30)
        mem = self._rnd.randint(100, 800)
        disk = self._rnd.uniform(0.5, 8.0)
        return cpu, mem, disk

    def _jitter(self, val: float, lo: float, hi: float, scale: float=0.1) -> float:
        delta = (self._rnd.random()*2-1) * scale * max(1.0, val)
        return max(lo, min(hi, val + delta))

    def _update_resources_for(self, p: Process):
        if p.state == ProcessState.RUNNING:
            p.cpu_usage = self._jitter(max(p.cpu_usage, p.cpu_base+10), 1, 100, 0.15)
            p.disk_usage = self._jitter(max(p.disk_usage, p.disk_base+1.0), 0.0, 60.0, 0.20)
            p.mem_usage  = int(self._jitter(max(p.mem_usage, p.mem_base), 50, 4096, 0.03))
        elif p.state in (ProcessState.READY, ProcessState.NEW):
            p.cpu_usage = self._jitter(max(1.0, p.cpu_base*0.8), 1, 50, 0.10)
            p.disk_usage = self._jitter(p.disk_base*0.7, 0.0, 20.0, 0.15)
            p.mem_usage  = int(self._jitter(p.mem_base, 50, 4096, 0.02))
        elif p.state in (ProcessState.BLOCKED, ProcessState.PAUSED):
            p.cpu_usage = self._jitter(2.0, 1, 20, 0.10)
            base_disk = p.disk_base * (1.5 if p.block_reason == BlockReason.IO else 0.5)
            p.disk_usage = self._jitter(base_disk, 0.0, 30.0, 0.12)
            p.mem_usage  = int(self._jitter(p.mem_base, 50, 4096, 0.01))
        elif p.state == ProcessState.FINISHED:
            # Finalizados: 0 consumo
            p.cpu_usage = 0.0
            p.disk_usage = 0.0
            p.mem_usage  = 0
        elif p.state == ProcessState.ZOMBIE:
            # Zombis: pequeñas cantidades
            p.cpu_usage = self._jitter(1.0, 0.0, 5.0, 0.10)
            p.disk_usage = self._jitter(0.2, 0.0, 2.0, 0.10)
            p.mem_usage  = int(self._jitter(min(128, max(10, p.mem_base*0.1)), 5, 256, 0.10))
        else:
            # Seguridad
            p.cpu_usage = self._jitter(1.0, 0.0, 5.0, 0.10)
            p.disk_usage = self._jitter(0.2, 0.0, 2.0, 0.10)
            p.mem_usage  = int(self._jitter(p.mem_base*0.5, 10, 4096, 0.01))

    # ---- API ----
    def system_empty(self) -> bool:
        return not (self.new or self.ready or self.running)

    def get_proc(self, pid: int) -> Optional[Process]:
        if self.running and self.running.pid == pid: return self.running
        for lst in (self.ready, self.blocked, self.new, self.finished, self.zombies):
            for p in lst:
                if p.pid == pid: return p
        return None

    def create_process(self, burst: int, name: Optional[str]=None) -> Process:
        if name is None or not str(name).strip():
            name = self._random_app_name()
        name = self.unique_name(str(name).strip())
        cpu, mem, disk = self._init_resources()
        p = Process(pid=self.next_pid, name=name, arrival_time=self.time,
                    burst_time=burst, remaining_time=burst,
                    cpu_base=cpu, mem_base=mem, disk_base=disk,
                    cpu_usage=cpu, mem_usage=mem, disk_usage=disk)
        self.next_pid += 1
        self.new.append(p)
        return p

    def set_priority(self, pid: int, prio: Priority) -> bool:
        p = self.get_proc(pid)
        if not p: return False
        p.priority = prio
        if self.running and self.running.pid == pid:
            self._quantum_used = 0
        return True

    def admit_all_new(self):
        if not self.new: return
        for p in list(self.new):
            p.set_state(ProcessState.READY)
            self.ready.append(p)
            self.new.remove(p)

    # ---- Weighted Round-Robin por CLASE ----
    def _advance_wrr(self):
        self._wrr_idx = (self._wrr_idx + 1) % len(self.PRIO_CYCLE)
        self._wrr_budget = self.WRR_WEIGHTS[self.PRIO_CYCLE[self._wrr_idx]]

    def _pop_ready_by_priority(self, prio: Priority) -> Optional[Process]:
        for idx, cand in enumerate(self.ready):
            if cand.priority == prio:
                if idx == 0: return self.ready.popleft()
                tmp = []
                for _ in range(idx): tmp.append(self.ready.popleft())
                p = self.ready.popleft()
                for it in reversed(tmp): self.ready.appendleft(it)
                return p
        return None

    def choose_next(self) -> Optional[Process]:
        if not self.ready: return None
        attempts = 0
        max_attempts = len(self.PRIO_CYCLE)*(max(self.WRR_WEIGHTS.values())+1)
        while attempts < max_attempts:
            current_class = self.PRIO_CYCLE[self._wrr_idx]
            has_candidate = any(p.priority == current_class for p in self.ready)
            if not has_candidate or self._wrr_budget <= 0:
                self._advance_wrr(); attempts += 1; continue
            p = self._pop_ready_by_priority(current_class)
            if p is None: self._advance_wrr(); attempts += 1; continue
            self._wrr_budget -= 1
            p.set_state(ProcessState.RUNNING); self._quantum_used = 0
            return p
        p = self.ready.popleft(); p.set_state(ProcessState.RUNNING); self._quantum_used = 0; return p

    # ---- Dependencias y zombis ----
    def _orphan_dependents(self, callee_pid: int):
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid == callee_pid:
                self.blocked.remove(p); p.block_reason=None; p.waiting_for_pid=None
                p.set_state(ProcessState.ZOMBIE); self.zombies.append(p)

    def _preempt_running_if_needed(self):
        if not self.running: return
        max_q = PRIO_QUANTUM[self.running.priority]
        if self._quantum_used >= max_q and len(self.ready) > 0:
            self.running.set_state(ProcessState.READY)
            self.running.block_reason=None; self.running.waiting_for_pid=None; self.running.io_remaining=0
            self.ready.append(self.running); self.running=None

    def tick(self, auto_arrivals: bool, auto_blocks: bool):
        self.time += 1

        # Llegadas automáticas
        if auto_arrivals:
            active = (1 if self.running else 0) + len(self.ready) + len(self.blocked)
            if active > 0:
                if self._rnd.random() < 0.05:  # 5% por tick
                    self.create_process(burst=self._rnd.randint(3, 10))
                self._spawned_when_empty = False
            else:
                if not self._spawned_when_empty:
                    self.create_process(burst=self._rnd.randint(3, 10))
                    self._spawned_when_empty = True

        # Admitir NEW
        self.admit_all_new()

        # Desbloqueo I/O
        for p in list(self.blocked):
            if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                p.io_remaining -= 1
                if p.io_remaining <= 0:
                    p.block_reason=None; p.set_state(ProcessState.READY)
                    self.blocked.remove(p); self.ready.append(p)

        # Desbloqueo por respuesta
        self._unblock_by_replies()

        # Revivir para ciclar
        if self.repeat_mode and (not self.ready and self.running is None) and (self.finished or self.zombies):
            self.revive_for_cycle(include_zombies=True)

        # Despacho
        if self.running is None:
            self.running = self.choose_next()

        # Ejecutar
        if self.running:
            self._unblock_dependents_of(self.running.pid)
            if auto_blocks and self._rnd.random() < 0.04:
                self.block_running(BlockReason.IO)
            else:
                self.running.remaining_time -= 1; self._quantum_used += 1
                if self.running.remaining_time <= 0:
                    self._finish_running()
                else:
                    self._preempt_running_if_needed()

        # Actualizar consumo simulado
        for p in self._all_processes():
            self._update_resources_for(p)

    def block_running(self, reason: BlockReason):
        if not self.running: return False
        self.running.set_state(ProcessState.PAUSED if reason == BlockReason.PAUSED else ProcessState.BLOCKED)
        self.running.block_reason = reason
        if reason == BlockReason.IO:
            self.running.io_remaining = self._rnd.randint(3, 10)
        self.blocked.append(self.running); self.running = None; return True

    def pause_running(self): return self.block_running(BlockReason.PAUSED)

    def unblock_pid(self, pid: int) -> bool:
        for p in list(self.blocked):
            if p.pid == pid:
                self.blocked.remove(p); p.block_reason=None; p.waiting_for_pid=None; p.io_remaining=0
                p.set_state(ProcessState.READY); self.ready.append(p); return True
        return False

    def _finish_running(self):
        if not self.running: return
        if self.repeat_mode:
            self.running.remaining_time = self.running.burst_time; self.running.set_state(ProcessState.READY); self.ready.append(self.running)
        else:
            done_pid = self.running.pid
            if self.simulate_zombie:
                self.running.set_state(ProcessState.ZOMBIE); self.zombies.append(self.running); self._orphan_dependents(done_pid)
            else:
                self.running.set_state(ProcessState.FINISHED); self.finished.append(self.running); self._orphan_dependents(done_pid)
        self.running=None

    def revive_for_cycle(self, include_zombies: bool=False):
        n=0
        for p in list(self.finished):
            self.finished.remove(p); p.remaining_time=p.burst_time; p.set_state(ProcessState.READY); self.ready.append(p); n+=1
        if include_zombies:
            for p in list(self.zombies):
                self.zombies.remove(p); p.remaining_time=p.burst_time; p.set_state(ProcessState.READY); self.ready.append(p); n+=1
        return n

    def finalize_pid(self, pid: int) -> bool:
        def finish_to_state(proc: Process):
            if self.simulate_zombie: proc.set_state(ProcessState.ZOMBIE); self.zombies.append(proc)
            else: proc.set_state(ProcessState.FINISHED); self.finished.append(proc)

        if self.running and self.running.pid == pid:
            finish_to_state(self.running); self._orphan_dependents(pid); self.running=None; return True
        for p in list(self.ready):
            if p.pid == pid: self.ready.remove(p); finish_to_state(p); self._orphan_dependents(pid); return True
        for p in list(self.blocked):
            if p.pid == pid: self.blocked.remove(p); p.block_reason=None; p.waiting_for_pid=None; p.io_remaining=0; finish_to_state(p); self._orphan_dependents(pid); return True
        for p in list(self.zombies):
            if p.pid == pid: self.zombies.remove(p); p.set_state(ProcessState.FINISHED); self.finished.append(p); return True
        for p in list(self.finished):
            if p.pid == pid: self.finished.remove(p); finish_to_state(p); self._orphan_dependents(pid); return True
        return False

    def depend_on(self, caller_pid: int, callee_pid: int):
        p = self.get_proc(caller_pid)
        if not p: return False
        p.block_reason = BlockReason.DEPENDENCY; p.waiting_for_pid = callee_pid
        if self.running and self.running.pid == caller_pid:
            self.block_running(BlockReason.DEPENDENCY)
        else:
            try: self.ready.remove(p)
            except ValueError: pass
            p.set_state(ProcessState.BLOCKED); self.blocked.append(p)
        return True

    def reply(self, from_pid: int, to_pid: int, msg: str="OK"):
        self.mailboxes[to_pid].append((from_pid, msg, self.time))

    def _unblock_by_replies(self):
        if not self.blocked: return
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid is not None:
                inbox = self.mailboxes.get(p.pid, [])
                idx = next((i for i,(src,_m,_t) in enumerate(inbox) if src == p.waiting_for_pid), None)
                if idx is not None:
                    inbox.pop(idx); p.block_reason=None; p.waiting_for_pid=None; p.set_state(ProcessState.READY); self.blocked.remove(p); self.ready.append(p)

    def _unblock_dependents_of(self, callee_pid: int):
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid == callee_pid:
                self.blocked.remove(p); p.block_reason=None; p.waiting_for_pid=None; p.set_state(ProcessState.READY); self.ready.append(p)

    def reap_zombies(self):
        for p in list(self.zombies):
            p.set_state(ProcessState.FINISHED); self.zombies.remove(p); self.finished.append(p)

    def reset(self, keep_options: bool=True):
        simz = self.simulate_zombie if keep_options else False
        rep = self.repeat_mode if keep_options else True
        self.__init__(simulate_zombie=simz, repeat_mode=rep)

# ---------------- Ventana principal ----------------
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Simulador — Estados de los Procesos")
        self.scheduler = Scheduler(simulate_zombie=False, repeat_mode=True)
        self.timer = QTimer(self); self.timer.timeout.connect(self.on_tick)
        self.init_ui()

    def init_ui(self):
        root = QWidget(); self.setCentralWidget(root); self.setMinimumSize(1200, 650)
        self.lbl_time = QLabel("Tiempo: 0"); self.lbl_running = QLabel("EJECUCIÓN: -")

        header_bar = QHBoxLayout(); header_bar.addStretch(1)
        self.btn_toggle_view = QToolButton(); self.btn_toggle_view.setCheckable(True); self.btn_toggle_view.setAutoRaise(True)
        self.btn_toggle_view.setFixedSize(26, 26); self.btn_toggle_view.setIconSize(QSize(18, 18))
        self.btn_toggle_view.setToolTip("Alternar vista por estados")
        self.btn_toggle_view.setIcon(self.style().standardIcon(QStyle.SP_FileDialogListView))
        self.btn_toggle_view.setStyleSheet("QToolButton { border: none; border-radius: 6px; padding: 2px; }"
                                           "QToolButton:checked { background-color: #3b82f6; }")
        self.btn_toggle_view.toggled.connect(self.on_toggle_view); header_bar.addWidget(self.btn_toggle_view)

        # Botones
        self.btn_add = QPushButton("Agregar proceso"); self.btn_add5 = QPushButton("Agregar 5 demo")
        self.btn_start = QPushButton("▶ Iniciar"); self.btn_pause = QPushButton("⏸ Pausar reloj")
        self.btn_step = QPushButton("⏭ Paso +1 tick"); self.btn_block = QPushButton("Bloquear ejecución (I/O)")
        self.btn_pause_proc = QPushButton("Pausar ejecución (manual)")
        self.btn_unblock = QPushButton("Reanudar/Desbloquear seleccionado"); self.btn_reap = QPushButton("Matar Zombis")
        self.btn_reset = QPushButton("Reiniciar")

        # Velocidad
        self.cmb_speed = QComboBox()
        for ms in [100, 200, 400, 800, 1000]:
            self.cmb_speed.addItem(f"{ms} ms/tick", ms)
        self.cmb_speed.setCurrentIndex(0)

        # Checks
        self.chk_zombie = QCheckBox("Simular estado Zombi"); self.chk_auto_arrivals = QCheckBox("Llegadas automáticas")
        self.chk_auto_blocks = QCheckBox("Bloqueos aleatorios")
        self.chk_repeat = QCheckBox("Modo repetición (ciclar procesos)"); self.chk_repeat.setChecked(True)

        # Control manual
        self.spn_target = QSpinBox(); self.spn_target.setWrapping(False); self.spn_target.setRange(1, 9999); self.spn_target.setPrefix("PID objetivo: ")
        self.btn_depend = QPushButton("Depender (EJECUCIÓN espera a PID)")

        self.cmb_priority = QComboBox(); self.cmb_priority.addItem("Seleccione una prioridad"); self.cmb_priority.addItems(["Alta","Media","Baja"]); self.cmb_priority.setCurrentIndex(0)
        self.cmb_priority.setToolTip("Cambiar prioridad del PID objetivo"); self.btn_apply_prio = QPushButton("Aplicar prioridad al PID")
        self.btn_finalize = QPushButton("Finalizar (PID objetivo)")

        # Conexiones
        self.btn_add.clicked.connect(self.on_add); self.btn_add5.clicked.connect(self.on_add5)
        self.btn_start.clicked.connect(self.on_start); self.btn_pause.clicked.connect(self.on_pause_clock)
        self.btn_step.clicked.connect(self.on_step); self.btn_block.clicked.connect(self.on_block_io)
        self.btn_pause_proc.clicked.connect(self.on_pause_proc); self.btn_unblock.clicked.connect(self.on_unblock_selected)
        self.btn_reap.clicked.connect(self.on_reap); self.btn_reset.clicked.connect(self.on_reset)
        self.cmb_speed.currentIndexChanged.connect(self.on_speed_changed)
        self.chk_zombie.stateChanged.connect(self.on_toggle_zombie)
        self.chk_auto_arrivals.stateChanged.connect(self.on_toggle_auto_arrivals)
        self.chk_auto_blocks.stateChanged.connect(self.on_toggle_auto_blocks)
        self.chk_repeat.stateChanged.connect(self.on_toggle_repeat)
        self.btn_depend.clicked.connect(self.on_depend)
        self.btn_apply_prio.clicked.connect(self.on_apply_priority)
        self.btn_finalize.clicked.connect(self.on_finalize)

        for b in [self.btn_add, self.btn_add5, self.btn_start, self.btn_pause, self.btn_step, self.btn_block, self.btn_pause_proc,
                  self.btn_unblock, self.btn_depend, self.btn_apply_prio, self.btn_finalize, self.btn_reap, self.btn_reset]:
            b.setMinimumHeight(32); b.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        controls_layout = QVBoxLayout(); controls_layout.addLayout(header_bar)
        controls_layout.addWidget(self.lbl_time); controls_layout.addWidget(self.lbl_running)
        controls_layout.addWidget(self.cmb_speed); controls_layout.addWidget(self.chk_zombie)
        controls_layout.addWidget(self.chk_auto_arrivals); controls_layout.addWidget(self.chk_auto_blocks)
        controls_layout.addWidget(self.chk_repeat)
        controls_layout.addWidget(self.btn_add); controls_layout.addWidget(self.btn_add5)
        controls_layout.addWidget(self.btn_start); controls_layout.addWidget(self.btn_pause)
        controls_layout.addWidget(self.btn_step); controls_layout.addWidget(self.btn_block)
        controls_layout.addWidget(self.btn_pause_proc)
        # NOTA: btn_unblock lo pasamos al panel de control manual

        manual_box = QGroupBox("Control manual de Procesos"); vb = QVBoxLayout()
        vb.addWidget(self.spn_target); vb.addWidget(self.btn_depend)
        vb.addWidget(self.btn_unblock); vb.addWidget(self.btn_finalize)
        # Prioridad: al final con placeholder
        vb.addWidget(self.cmb_priority); vb.addWidget(self.btn_apply_prio)
        manual_box.setLayout(vb); controls_layout.addWidget(manual_box)

        controls_layout.addWidget(self.btn_reap); controls_layout.addWidget(self.btn_reset); controls_layout.addStretch(1)

        controls_box = QGroupBox("Controles"); controls_box.setLayout(controls_layout)
        controls_container = QWidget(); vwrap = QVBoxLayout(controls_container); vwrap.addWidget(controls_box); vwrap.setContentsMargins(0,0,0,0)
        scroll = QScrollArea(); scroll.setWidgetResizable(True); scroll.setWidget(controls_container); scroll.setMinimumWidth(360); scroll.setMaximumWidth(420)

        headers = ["PID","Nombre","Estado","Ticks restantes","Razón","Esperando PID","Prioridad","CPU %","Memoria MB","Disco MB/s"]
        self.tbl_all = QTableWidget(0, len(headers)); self.tbl_all.setHorizontalHeaderLabels(headers)
        self.tbl_all.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)

        processes_box = QGroupBox("Procesos"); pv = QVBoxLayout()

        self.unified_container = QWidget(); uvl = QVBoxLayout(self.unified_container); uvl.setContentsMargins(0,0,0,0); uvl.addWidget(self.tbl_all)
        self.grouped_container = QWidget(); gvl = QVBoxLayout(self.grouped_container); gvl.setContentsMargins(0,0,0,0)

        self.tbl_ready = QTableWidget(0, len(headers)); self.tbl_ready.setHorizontalHeaderLabels(headers)
        self.tbl_ready.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_rr = QGroupBox("EJECUCIÓN + READY"); lay_rr = QVBoxLayout(); lay_rr.addWidget(self.tbl_ready); box_rr.setLayout(lay_rr); gvl.addWidget(box_rr)

        self.tbl_blocked = QTableWidget(0, len(headers)); self.tbl_blocked.setHorizontalHeaderLabels(headers)
        self.tbl_blocked.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_bp = QGroupBox("BLOQUEADO + PAUSADO"); lay_bp = QVBoxLayout(); lay_bp.addWidget(self.tbl_blocked); box_bp.setLayout(lay_bp); gvl.addWidget(box_bp)

        self.tbl_done = QTableWidget(0, len(headers)); self.tbl_done.setHorizontalHeaderLabels(headers)
        self.tbl_done.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_dz = QGroupBox("FINALIZADO + ZOMBIE"); lay_dz = QVBoxLayout(); lay_dz.addWidget(self.tbl_done); box_dz.setLayout(lay_dz); gvl.addWidget(box_dz)

        self.grouped_container.hide(); pv.addWidget(self.unified_container); pv.addWidget(self.grouped_container); processes_box.setLayout(pv)

        layout = QHBoxLayout(); layout.addWidget(scroll, 0); layout.addWidget(processes_box, 1); root.setLayout(layout)
        self.update_pid_spin_range(); self.refresh_table_all()

    def update_labels(self):
        self.lbl_time.setText(f"Tiempo: {self.scheduler.time}")
        if self.scheduler.running:
            self.lbl_running.setText(f"EJECUCIÓN: PID {self.scheduler.running.pid} ({self.scheduler.running.name}) (restante={self.scheduler.running.remaining_time}, prio={PRIO_LABEL[self.scheduler.running.priority]})")
        else:
            self.lbl_running.setText("EJECUCIÓN: -")

    def update_pid_spin_range(self):
        max_pid = max(1, self.scheduler.next_pid - 1); self.spn_target.setRange(1, max_pid)
        if self.spn_target.value() > max_pid: self.spn_target.setValue(max_pid)

    # ---- eventos ----
    def on_add(self):
        name, ok = QInputDialog.getText(self, "Nuevo proceso", "Nombre del proceso:")
        if not ok or not str(name).strip(): name = None
        burst = random.randint(3, 10); self.scheduler.create_process(burst, name=name)
        self.scheduler.admit_all_new()
        if self.scheduler.running is None: self.scheduler.running = self.scheduler.choose_next()
        self.update_pid_spin_range(); self.refresh_current_view()

    def on_add5(self):
        for _ in range(5):
            self.scheduler.create_process(random.randint(3, 10), name=self.scheduler._random_app_name())
        self.scheduler.admit_all_new()
        if self.scheduler.running is None: self.scheduler.running = self.scheduler.choose_next()
        self.update_pid_spin_range(); self.refresh_current_view()

    def _speed_ms(self) -> int:
        data = self.cmb_speed.currentData()
        if data is None:
            try: return int(self.cmb_speed.currentText().split()[0])
            except Exception: return 200
        return int(data)

    def on_start(self):
        if self.chk_auto_arrivals.isChecked() and self.scheduler.system_empty():
            self.scheduler.create_process(burst=random.randint(3, 10), name=self.scheduler._random_app_name())
            self.scheduler.admit_all_new()
        self.scheduler.repeat_mode = self.chk_repeat.isChecked()
        if not self.timer.isActive(): self.timer.start(self._speed_ms())
        self.refresh_current_view()

    def on_pause_clock(self): self.timer.stop()

    def on_step(self):
        if self.timer.isActive(): self.timer.stop()
        self.on_tick()

    def on_block_io(self): self.scheduler.block_running(BlockReason.IO); self.refresh_current_view()
    def on_pause_proc(self): self.scheduler.pause_running(); self.refresh_current_view()

    def on_unblock_selected(self):
        pid = self.spn_target.value()
        if not self.scheduler.unblock_pid(pid):
            QMessageBox.information(self, "Info", f"PID {pid} no está en estado bloqueado/pausado/dependiendo.")
        self.refresh_current_view()

    def on_reap(self): self.scheduler.reap_zombies(); self.refresh_current_view()

    def on_reset(self):
        self.timer.stop(); self.scheduler.reset(keep_options=True)
        self.update_pid_spin_range(); self.refresh_current_view()

    def on_speed_changed(self, _):
        if self.timer.isActive(): self.timer.start(self._speed_ms())

    def on_toggle_zombie(self, _state): self.scheduler.simulate_zombie = self.chk_zombie.isChecked()

    def on_toggle_auto_arrivals(self, _state):
        if self.chk_auto_arrivals.isChecked() and self.scheduler.system_empty():
            self.scheduler.create_process(burst=random.randint(3, 10), name=self.scheduler._random_app_name())
            self.scheduler.admit_all_new()
            if self.scheduler.running is None: self.scheduler.running = self.scheduler.choose_next()
            self.update_pid_spin_range(); self.refresh_current_view()

    def on_toggle_auto_blocks(self, _state): pass

    def on_toggle_repeat(self, _state):
        checked = self.chk_repeat.isChecked(); self.scheduler.repeat_mode = checked
        if checked: self.scheduler.revive_for_cycle(include_zombies=True)
        self.refresh_current_view()

    def on_depend(self):
        if not self.scheduler.running:
            QMessageBox.information(self, "Info", "No hay proceso en EJECUCIÓN para establecer dependencia."); return
        callee = self.spn_target.value(); caller = self.scheduler.running.pid
        if caller == callee:
            QMessageBox.warning(self, "Aviso", "Un proceso no puede depender de sí mismo."); return
        if not self.scheduler.depend_on(caller_pid=caller, callee_pid=callee):
            QMessageBox.warning(self, "Aviso", "No se pudo establecer la dependencia.")
        self.refresh_current_view()

    def on_finalize(self):
        pid = self.spn_target.value()
        if not self.scheduler.finalize_pid(pid):
            QMessageBox.information(self, "Info", f"No se encontró el PID {pid} activo.")
        self.refresh_current_view()

    def on_apply_priority(self):
        pid = self.spn_target.value()
        idx = self.cmb_priority.currentIndex()
        if idx == 0:
            QMessageBox.information(self, "Info", "Seleccione una prioridad para aplicar.")
            return
        text = self.cmb_priority.currentText()
        prio = Priority.MEDIUM
        if text == "Alta": prio = Priority.HIGH
        elif text == "Baja": prio = Priority.LOW
        if not self.scheduler.set_priority(pid, prio):
            QMessageBox.information(self, "Info", f"No se encontró el PID {pid} activo.")
        # Volver al placeholder
        self.cmb_priority.setCurrentIndex(0)
        self.refresh_current_view()

    def on_tick(self):
        self.scheduler.simulate_zombie = self.chk_zombie.isChecked()
        self.scheduler.repeat_mode = self.chk_repeat.isChecked()
        auto_arrivals = self.chk_auto_arrivals.isChecked(); auto_blocks = self.chk_auto_blocks.isChecked()
        self.scheduler.tick(auto_arrivals=auto_arrivals, auto_blocks=auto_blocks)
        self.update_pid_spin_range(); self.refresh_current_view()

    def on_toggle_view(self, checked: bool):
        self.btn_toggle_view.setIcon(self.style().standardIcon(QStyle.SP_FileDialogDetailedView if checked else QStyle.SP_FileDialogListView))
        if checked: self.unified_container.hide(); self.grouped_container.show(); self.refresh_tables_grouped()
        else: self.grouped_container.hide(); self.unified_container.show(); self.refresh_table_all()

    # ---- refresco tablas ----
    def _state_text(self, st: ProcessState) -> str:
        return STATE_LABEL_ES.get(st, st.name)

    def _reason_text(self, br: Optional[BlockReason], io_remaining: int) -> str:
        if not br: return ""
        t = REASON_LABEL_ES.get(br, br.name)
        if br == BlockReason.IO and io_remaining > 0: t += f" ({io_remaining})"
        return t

    def _fill_table(self, tbl: QTableWidget, items: List[Process]):
        tbl.setRowCount(len(items))
        for r, p in enumerate(items):
            estado = self._state_text(p.state)
            razon = self._reason_text(p.block_reason, p.io_remaining)
            waitfor = str(p.waiting_for_pid) if p.waiting_for_pid is not None else ""
            prio = PRIO_LABEL[p.priority]
            cells = [str(p.pid), p.name, estado, str(p.remaining_time), razon, waitfor, prio,
                     f"{p.cpu_usage:.0f}", str(p.mem_usage), f"{p.disk_usage:.1f}"]
            for c, val in enumerate(cells):
                item = QTableWidgetItem(val)
                tbl.setItem(r, c, item)
                item.setBackground(QBrush(STATE_COLORS.get(p.state)))

    def refresh_tables_grouped(self):
        pro_running = [self.scheduler.running] if self.scheduler.running else []
        pro_ready = list(self.scheduler.ready)
        pro_blocked = [p for p in self.scheduler.blocked if p.block_reason in (BlockReason.IO, BlockReason.DEPENDENCY)]
        pro_paused = [p for p in self.scheduler.blocked if p.block_reason == BlockReason.PAUSED]
        pro_finished = list(self.scheduler.finished); pro_zombie = list(self.scheduler.zombies)
        self._fill_table(self.tbl_ready, [*pro_running, *pro_ready])
        self._fill_table(self.tbl_blocked, [*pro_blocked, *pro_paused])
        self._fill_table(self.tbl_done, [*pro_finished, *pro_zombie])

    def refresh_table_all(self):
        procs: List[Process] = []
        if self.scheduler.running: procs.append(self.scheduler.running)
        procs += list(self.scheduler.ready) + list(self.scheduler.blocked) + list(self.scheduler.zombies) + list(self.scheduler.finished) + list(self.scheduler.new)
        self._fill_table(self.tbl_all, procs)

    def refresh_current_view(self):
        """Refresca la vista activa y las etiquetas."""
        self.update_labels()
        if self.btn_toggle_view.isChecked():
            self.refresh_tables_grouped()
        else:
            self.refresh_table_all()

def main():
    import sys
    app = QApplication(sys.argv); w = MainWindow(); w.show(); sys.exit(app.exec())

if __name__ == "__main__":
    main()
