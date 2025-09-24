
# -*- coding: utf-8 -*-
'Simulador — Estados de los Procesos'

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
    QHeaderView, QVBoxLayout, QHBoxLayout, QGroupBox, QSizePolicy, QScrollArea, QToolButton, QStyle, QInputDialog
)

# --------- Constantes del simulador ---------
DEFAULT_TICK_MS = 800           # 1) velocidad por defecto
P_BLOCK_IO = 0.05               # 4) prob. de bloqueo I/O en cada tick del RUNNING
P_DEPEND_ON_ADMIT = 0.15        # 10) prob. de que un proceso adquiera dependencia al admitirse
P_DEPEND_REPLY = 0.45           # 10) prob. de que el RUNNING responda y libere a sus dependientes en un tick
P_FINISH_TO_ZOMBIE = 0.10       # 2) prob. de quedar en ZOMBIE al finalizar
FINISHED_TTL = 6                # 11) ticks que permanece visible un FINISHED

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
    BLOCKED = auto()    # Solo I/O o Dependencia
    FINISHED = auto()
    ZOMBIE = auto()

class BlockReason(Enum):
    IO = auto()
    DEPENDENCY = auto()

class Priority(Enum):
    HIGH = auto()
    MEDIUM = auto()
    LOW = auto()

PRIO_LABEL = {Priority.HIGH:"Alta", Priority.MEDIUM:"Media", Priority.LOW:"Baja"}
PRIO_QUANTUM = {Priority.HIGH:3, Priority.MEDIUM:2, Priority.LOW:1}  # ticks seguidos por proceso

STATE_COLORS = {
    ProcessState.NEW: QColor(66,135,245),
    ProcessState.READY: QColor(245,211,66),
    ProcessState.RUNNING: QColor(82,196,26),
    ProcessState.BLOCKED: QColor(255,159,28),
    ProcessState.FINISHED: QColor(120,120,120),
    ProcessState.ZOMBIE: QColor(220,38,38),
}

STATE_LABEL_ES = {
ProcessState.RUNNING: "Ejecución",
    ProcessState.READY: "Listo",
    ProcessState.BLOCKED: "Bloqueado",
    ProcessState.FINISHED: "Finalizado",

}
REASON_LABEL_ES = {
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
    # Consumos simulados (base y valores actuales)
    cpu_base: float = 0.0
    mem_base: int = 0
    disk_base: float = 0.0
    cpu_usage: float = 0.0
    mem_usage: int = 0
    disk_usage: float = 0.0
    # Marcas y tiempos
    finished_at: Optional[int] = None   # 11) cuándo pasó a FINISHED (para limpieza)
    has_replied: bool = False           # 10) si ya "respondió" a dependientes (auto)
    has_executed: bool = False          # para métricas de dependencias

    def set_state(self, st: ProcessState):
        self.state = st

# ---------------- Planificador ----------------
class Scheduler:
    # 9) Prioridades se asignan automáticamente; se mantiene RR con pesos por clase
    WRR_WEIGHTS = {Priority.HIGH:2, Priority.MEDIUM:1, Priority.LOW:1}
    PRIO_CYCLE = [Priority.HIGH, Priority.MEDIUM, Priority.LOW]

    def __init__(self):
        self.time: int = 0
        self.next_pid: int = 1

        self.new: List[Process] = []
        self.ready: Deque[Process] = deque()
        self.blocked: List[Process] = []
        self.finished: List[Process] = []
        self.zombies: List[Process] = []
        self.running: Optional[Process] = None

        self._rnd = random.Random()
        self._quantum_used: int = 0

        # Estado del WRR por clase
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
        # Valores base razonables
        cpu = self._rnd.uniform(5, 30)
        mem = self._rnd.randint(100, 800)
        disk = self._rnd.uniform(0.5, 8.0)
        return cpu, mem, disk

    def _jitter(self, val: float, lo: float, hi: float, scale: float=0.1) -> float:
        delta = (self._rnd.random()*2-1) * scale * max(1.0, val)
        return max(lo, min(hi, val + delta))

    def _update_resources_for(self, p: Process):
        # 1) RUNNING sube consumo; 2) READY/NEW bajo; 3) BLOCKED depende; 4) FINISHED=0; 5) ZOMBIE poco
        if p.state == ProcessState.RUNNING:
            p.cpu_usage = self._jitter(max(p.cpu_usage, p.cpu_base+10), 1, 100, 0.15)
            p.disk_usage = self._jitter(max(p.disk_usage, p.disk_base+1.0), 0.0, 60.0, 0.20)
            p.mem_usage  = int(self._jitter(max(p.mem_usage, p.mem_base), 50, 4096, 0.03))
        elif p.state in (ProcessState.READY, ProcessState.NEW):
            p.cpu_usage = self._jitter(max(1.0, p.cpu_base*0.8), 1, 50, 0.10)
            p.disk_usage = self._jitter(p.disk_base*0.7, 0.0, 20.0, 0.15)
            p.mem_usage  = int(self._jitter(p.mem_base, 50, 4096, 0.02))
        elif p.state == ProcessState.BLOCKED:
            p.cpu_usage = 0.0
            base_disk = p.disk_base * (1.5 if p.block_reason == BlockReason.IO else 0.5)
            p.disk_usage = self._jitter(base_disk, 0.0, 30.0, 0.12)
            p.mem_usage  = int(self._jitter(p.mem_base, 50, 4096, 0.01))
        elif p.state == ProcessState.FINISHED:
            p.cpu_usage = 0.0; p.disk_usage = 0.0; p.mem_usage = 0
        elif p.state == ProcessState.ZOMBIE:
            p.cpu_usage = self._jitter(1.0, 0.0, 5.0, 0.10)
            p.disk_usage = self._jitter(0.2, 0.0, 2.0, 0.10)
            p.mem_usage  = int(self._jitter(min(128, max(10, p.mem_base*0.1)), 5, 256, 0.10))

    # ---- API pública ----
    def system_empty(self) -> bool:
        return not (self.new or self.ready or self.running)

    def get_proc(self, pid: int) -> Optional[Process]:
        if self.running and self.running.pid == pid: return self.running
        for lst in (self.ready, self.blocked, self.new, self.finished, self.zombies):
            for p in lst:
                if p.pid == pid: return p
        return None

    def create_process(self, burst: int, name: Optional[str]=None) -> Process:
        """Crea un proceso con nombre (o aleatorio) y prioridad **automática**."""
        if name is None or not str(name).strip():
            name = self._random_app_name()
        name = self.unique_name(str(name).strip())
        cpu, mem, disk = self._init_resources()
        # 9) Prioridad automática
        prio = random.choice([Priority.HIGH, Priority.MEDIUM, Priority.LOW])
        p = Process(pid=self.next_pid, name=name, arrival_time=self.time,
                    burst_time=burst, remaining_time=burst, priority=prio,
                    cpu_base=cpu, mem_base=mem, disk_base=disk,
                    cpu_usage=cpu, mem_usage=mem, disk_usage=disk)
        self.next_pid += 1
        self.new.append(p)
        return p

    def admit_all_new(self):
        """Admite NEW a READY y aplica 10) prob. de dependencia automática."""
        if not self.new: return
        active_pids = [q.pid for q in ( ([self.running] if self.running else []) + list(self.ready) + self.blocked )]
        for p in list(self.new):
            p.set_state(ProcessState.READY)
            self.ready.append(p)
            self.new.remove(p)
            # 10) Dependencia automática al admitirse
            if active_pids and random.random() < P_DEPEND_ON_ADMIT:
                target_pid = random.choice(active_pids)
                self._set_dependency(p, target_pid)

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

    # ---- Dependencias automáticas ----
    def _set_dependency(self, p: Process, target_pid: int):
        """Bloquea p por dependencia hacia target_pid."""
        try:
            self.ready.remove(p)
        except ValueError:
            pass
        p.block_reason = BlockReason.DEPENDENCY
        p.waiting_for_pid = target_pid
        p.set_state(ProcessState.BLOCKED)
        self.blocked.append(p)

    def _auto_reply_from(self, pid: int):
        """10) Con probabilidad, el RUNNING 'responde' y libera a dependientes que lo esperan."""
        if random.random() >= P_DEPEND_REPLY: return
        for q in list(self.blocked):
            if q.block_reason == BlockReason.DEPENDENCY and q.waiting_for_pid == pid:
                self.blocked.remove(q)
                q.block_reason = None; q.waiting_for_pid = None
                q.set_state(ProcessState.READY)
                self.ready.append(q)

    def _zombify_waiters_of(self, pid: int):
        """10) Si el proceso objetivo finaliza sin responder, dependientes -> ZOMBIE."""
        for q in list(self.blocked):
            if q.block_reason == BlockReason.DEPENDENCY and q.waiting_for_pid == pid:
                self.blocked.remove(q)
                q.block_reason = None; q.waiting_for_pid = None
                q.set_state(ProcessState.ZOMBIE)
                self.zombies.append(q)

    # ---- Ciclo de reloj ----
    def _preempt_running_if_needed(self):
        if not self.running: return
        max_q = PRIO_QUANTUM[self.running.priority]
        if self._quantum_used >= max_q and len(self.ready) > 0:
            self.running.set_state(ProcessState.READY)
            self.ready.append(self.running); self.running=None

    def tick(self):
        """Avanza un tick de reloj: admite NEW, programa, ejecuta, bloquea/finzaliza y actualiza recursos."""
        self.time += 1

        # Admitir NEW (y posibles dependencias automáticas)
        self.admit_all_new()

        # Desbloquear por I/O que termina
        for p in list(self.blocked):
            if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                p.io_remaining -= 1
                if p.io_remaining <= 0:
                    self.blocked.remove(p)
                    p.block_reason=None; p.set_state(ProcessState.READY)
                    self.ready.append(p)

        # Despacho
        if self.running is None:
            self.running = self.choose_next()

        # Ejecutar el RUNNING
        if self.running:
            self.running.has_executed = True
            # 10) posibilidad de responder a dependientes cada tick
            self._auto_reply_from(self.running.pid)

            # 4) bloqueos I/O siempre con prob. fija
            if random.random() < P_BLOCK_IO:
                self.running.block_reason = BlockReason.IO
                self.running.io_remaining = random.randint(3, 8)
                self.running.set_state(ProcessState.BLOCKED)
                self.blocked.append(self.running); self.running = None
            else:
                # consumir un tick de CPU
                self.running.remaining_time -= 1; self._quantum_used += 1

                # ¿terminó?
                if self.running.remaining_time <= 0:
                    finished_pid = self.running.pid
                    if random.random() < P_FINISH_TO_ZOMBIE:
                        self.running.set_state(ProcessState.ZOMBIE)
                        self.zombies.append(self.running)
                    else:
                        self.running.set_state(ProcessState.FINISHED)
                        self.running.finished_at = self.time
                        self.finished.append(self.running)
                    # 10) dependientes que aún esperaban -> ZOMBIE
                    self._zombify_waiters_of(finished_pid)
                    self.running = None
                else:
                    self._preempt_running_if_needed()

        # 11) limpieza de FINISHED tras TTL
        for p in list(self.finished):
            if p.finished_at is not None and (self.time - p.finished_at) >= FINISHED_TTL:
                self.finished.remove(p)

        # Actualizar consumo simulado
        for p in self._all_processes():
            self._update_resources_for(p)

# ---------------- Ventana principal ----------------
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Simulador — Estados de los Procesos")
        self.scheduler = Scheduler()
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

        # Botones principales (se eliminaron los manuales y opciones de configuración)
        self.btn_add = QPushButton("Agregar proceso")
        self.btn_start = QPushButton("▶ Iniciar"); self.btn_pause = QPushButton("⏸ Pausar reloj")
        self.btn_step = QPushButton("⏭ Paso +1 tick")
        self.btn_reset = QPushButton("Reiniciar")

        # Conexiones
        self.btn_add.clicked.connect(self.on_add)
        self.btn_start.clicked.connect(self.on_start)
        self.btn_pause.clicked.connect(self.on_pause_clock)
        self.btn_step.clicked.connect(self.on_step)
        self.btn_reset.clicked.connect(self.on_reset)

        for b in [self.btn_add, self.btn_start, self.btn_pause, self.btn_step, self.btn_reset]:
            b.setMinimumHeight(32); b.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Panel de controles
        controls_layout = QVBoxLayout(); controls_layout.addLayout(header_bar)
        controls_layout.addWidget(self.lbl_time); controls_layout.addWidget(self.lbl_running)
        controls_layout.addWidget(self.btn_add)
        controls_layout.addWidget(self.btn_start); controls_layout.addWidget(self.btn_pause)
        controls_layout.addWidget(self.btn_step)
        controls_layout.addWidget(self.btn_reset); controls_layout.addStretch(1)

        controls_box = QGroupBox("Controles"); controls_box.setLayout(controls_layout)
        controls_container = QWidget(); vwrap = QVBoxLayout(controls_container); vwrap.addWidget(controls_box); vwrap.setContentsMargins(0,0,0,0)
        scroll = QScrollArea(); scroll.setWidgetResizable(True); scroll.setWidget(controls_container); scroll.setMinimumWidth(360); scroll.setMaximumWidth(420)

        # Tabla unificada y vista por secciones
        headers = ["PID","Nombre","Estado","Ticks restantes","Razón","Esperando PID","Prioridad","CPU %","Memoria MB","Disco MB/s"]
        self.tbl_all = QTableWidget(0, len(headers)); self.tbl_all.setHorizontalHeaderLabels(headers)
        self.tbl_all.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)

        processes_box = QGroupBox("Procesos"); pv = QVBoxLayout()

        self.unified_container = QWidget(); uvl = QVBoxLayout(self.unified_container); uvl.setContentsMargins(0,0,0,0); uvl.addWidget(self.tbl_all)
        self.grouped_container = QWidget(); gvl = QVBoxLayout(self.grouped_container); gvl.setContentsMargins(0,0,0,0)

        self.tbl_ready = QTableWidget(0, len(headers)); self.tbl_ready.setHorizontalHeaderLabels(headers)
        self.tbl_ready.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_rr = QGroupBox("EJECUCIÓN + Listo"); lay_rr = QVBoxLayout(); lay_rr.addWidget(self.tbl_ready); box_rr.setLayout(lay_rr); gvl.addWidget(box_rr)

        self.tbl_blocked = QTableWidget(0, len(headers)); self.tbl_blocked.setHorizontalHeaderLabels(headers)
        self.tbl_blocked.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_bp = QGroupBox("BLOQUEADO"); lay_bp = QVBoxLayout(); lay_bp.addWidget(self.tbl_blocked); box_bp.setLayout(lay_bp); gvl.addWidget(box_bp)

        self.tbl_done = QTableWidget(0, len(headers)); self.tbl_done.setHorizontalHeaderLabels(headers)
        self.tbl_done.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_dz = QGroupBox("FINALIZADO + ZOMBIE"); lay_dz = QVBoxLayout(); lay_dz.addWidget(self.tbl_done); box_dz.setLayout(lay_dz); gvl.addWidget(box_dz)

        self.grouped_container.hide(); pv.addWidget(self.unified_container); pv.addWidget(self.grouped_container); processes_box.setLayout(pv)

        layout = QHBoxLayout(); layout.addWidget(scroll, 0); layout.addWidget(processes_box, 1); root.setLayout(layout)
        self.refresh_table_all()

    # ---- Eventos UI ----
    def on_add(self):
        """Agregar proceso: pide nombre (opcional) y usa nombre aleatorio si está vacío."""
        name, ok = QInputDialog.getText(self, "Nuevo proceso", "Nombre del proceso:")
        if not ok or not str(name).strip(): name = None
        burst = random.randint(7, 15)
        self.scheduler.create_process(burst, name=name)
        self.scheduler.admit_all_new()
        if self.scheduler.running is None: self.scheduler.running = self.scheduler.choose_next()
        self.refresh_current_view()

    def on_start(self):
        """Inicia el reloj a 800 ms/tick."""
        if not self.timer.isActive():
            self.timer.start(DEFAULT_TICK_MS)
        self.refresh_current_view()

    def on_pause_clock(self):
        self.timer.stop()

    def on_step(self):
        if self.timer.isActive(): self.timer.stop()
        self.on_tick()

    def on_reset(self):
        self.timer.stop(); self.scheduler = Scheduler()
        self.refresh_current_view()

    # ---- Ticker ----
    def on_tick(self):
        self.scheduler.tick()
        self.refresh_current_view()

    # ---- Vista ----
    def on_toggle_view(self, checked: bool):
        self.btn_toggle_view.setIcon(self.style().standardIcon(QStyle.SP_FileDialogDetailedView if checked else QStyle.SP_FileDialogListView))
        if checked: self.unified_container.hide(); self.grouped_container.show(); self.refresh_tables_grouped()
        else: self.grouped_container.hide(); self.unified_container.show(); self.refresh_table_all()

    # ---- refresco tablas ----
    def update_labels(self):
        self.lbl_time.setText(f"Tiempo: {self.scheduler.time}")
        if self.scheduler.running:
            self.lbl_running.setText(f"EJECUCIÓN: PID {self.scheduler.running.pid} ({self.scheduler.running.name}) (restante={self.scheduler.running.remaining_time}, prio={PRIO_LABEL[self.scheduler.running.priority]})")
        else:
            self.lbl_running.setText("EJECUCIÓN: -")

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
        pro_blocked = list(self.scheduler.blocked)
        pro_finished = list(self.scheduler.finished); pro_zombie = list(self.scheduler.zombies)
        self._fill_table(self.tbl_ready, [*pro_running, *pro_ready])
        self._fill_table(self.tbl_blocked, [*pro_blocked])
        self._fill_table(self.tbl_done, [*pro_finished, *pro_zombie])

    def refresh_table_all(self):
        procs: List[Process] = []
        if self.scheduler.running: procs.append(self.scheduler.running)
        procs += list(self.scheduler.ready) + list(self.scheduler.blocked) + list(self.scheduler.zombies) + list(self.scheduler.finished) + list(self.scheduler.new)
        self._fill_table(self.tbl_all, procs)

    def refresh_current_view(self):
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
