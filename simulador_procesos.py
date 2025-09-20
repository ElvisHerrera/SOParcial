
# -*- coding: utf-8 -*-
"""
Simulador — Vista Única (FCFS + Dependencias + Control manual)

Características implementadas (resumen):
- Vista única o vista separada en 3 tablas (RUNNING+READY / BLOCKED+PAUSED / FINISHED+ZOMBIE) con botón de alternar (icon-only).
- FCFS.
- Llegadas automáticas: si está vacío y la opción está ON, crea 1 proceso; si hay procesos activos, 10%/tick.
- Bloqueos aleatorios (I/O): 20%/tick. El I/O tiene duración aleatoria de 3–10 ticks (visible como IO (n)).
  Al llegar a 0, el proceso vuelve a READY automáticamente.
- Dependencias: RUNNING puede depender de un PID; queda BLOQUEADO (DEPENDENCY) hasta que ese PID responda.
- Zombi por dependencia huérfana: si finaliza el PID del que dependo, paso a ZOMBIE.
- Modo Repetición: al terminar un proceso, vuelve a READY con ráfaga original. Al activar la casilla,
  reanima FINISHED y ZOMBIE a READY para reanudar el ciclo.
- Botón “Reanudar/Desbloquear seleccionado”: usa el PID objetivo para desbloquear (y si ese PID está en PAUSED/IO/DEPENDENCY, vuelve a READY).
- Finalizar (PID objetivo): si está ON “Simular estado Zombi”, el proceso pasa a ZOMBIE; en caso contrario, a FINISHED.
"""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum, auto
from typing import Optional, Deque, List, Dict, Tuple
from collections import deque, defaultdict
import random

from PySide6.QtCore import Qt, QTimer, QSize
from PySide6.QtGui import QColor
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QPushButton, QTableWidget, QTableWidgetItem,
    QHeaderView, QVBoxLayout, QHBoxLayout, QGroupBox, QMessageBox, QComboBox, QCheckBox, QSpinBox,
    QSizePolicy, QScrollArea, QToolButton, QStyle
)

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

STATE_COLORS = {
    ProcessState.NEW: QColor(66, 135, 245),
    ProcessState.READY: QColor(245, 211, 66),
    ProcessState.RUNNING: QColor(82, 196, 26),
    ProcessState.BLOCKED: QColor(255, 159, 28),
    ProcessState.PAUSED: QColor(128, 90, 213),
    ProcessState.FINISHED: QColor(120, 120, 120),
    ProcessState.ZOMBIE: QColor(220, 38, 38),
}

@dataclass
class Process:
    pid: int
    arrival_time: int
    burst_time: int
    remaining_time: int
    state: ProcessState = ProcessState.NEW
    block_reason: Optional[BlockReason] = None
    waiting_for_pid: Optional[int] = None
    io_remaining: int = 0  # duración restante en ticks cuando está en IO

    def set_state(self, st: ProcessState):
        self.state = st

class Scheduler:
    def __init__(self, simulate_zombie: bool = False, repeat_mode: bool = True):
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
        self.mailboxes: Dict[int, List[Tuple[int, str, int]]] = defaultdict(list)
        self._spawned_when_empty = False  # para llegadas automáticas (solo una vez en vacío)

    # Helpers
    def system_empty(self) -> bool:
        return not (self.new or self.ready or self.running)

    def get_proc(self, pid: int) -> Optional[Process]:
        if self.running and self.running.pid == pid:
            return self.running
        for lst in (self.ready, self.blocked, self.new, self.finished, self.zombies):
            for p in lst:
                if p.pid == pid:
                    return p
        return None

    def create_process(self, burst: int) -> Process:
        p = Process(pid=self.next_pid, arrival_time=self.time, burst_time=burst, remaining_time=burst)
        self.next_pid += 1
        self.new.append(p)
        return p

    def admit_all_new(self):
        for p in list(self.new):
            p.set_state(ProcessState.READY)
            self.ready.append(p)
            self.new.remove(p)

    def choose_next(self) -> Optional[Process]:
        if not self.ready:
            return None
        p = self.ready.popleft()
        p.set_state(ProcessState.RUNNING)
        return p

    def _orphan_dependents(self, callee_pid: int):
        """Cualquier proceso bloqueado esperando callee_pid pasa a ZOMBIE (orfandad)."""
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid == callee_pid:
                self.blocked.remove(p)
                p.block_reason = None
                p.waiting_for_pid = None
                p.set_state(ProcessState.ZOMBIE)
                self.zombies.append(p)

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

        self.admit_all_new()

        # Desbloqueo por I/O (contador en ticks)
        for p in list(self.blocked):
            if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                p.io_remaining -= 1
                if p.io_remaining <= 0:
                    p.block_reason = None
                    p.set_state(ProcessState.READY)
                    self.blocked.remove(p)
                    self.ready.append(p)

        # Dependencias (mensajes)
        self._unblock_by_replies()

        # Repeat ON: si no hay nada, revivir terminados/zombis para continuar el ciclo
        if self.repeat_mode and (not self.ready and self.running is None) and (self.finished or self.zombies):
            self.revive_for_cycle(include_zombies=True)

        if self.running is None:
            self.running = self.choose_next()

        if self.running:
            # Auto-desbloqueo de dependientes cuando el callee ejecuta al menos 1 tick
            self._unblock_dependents_of(self.running.pid)
            if auto_blocks and self._rnd.random() < 0.04:  # 4% por tick
                self.block_running(BlockReason.IO)
            else:
                self.running.remaining_time -= 1
                if self.running.remaining_time <= 0:
                    self._finish_running()

    def block_running(self, reason: BlockReason):
        if not self.running:
            return False
        self.running.set_state(ProcessState.PAUSED if reason==BlockReason.PAUSED else ProcessState.BLOCKED)
        self.running.block_reason = reason
        if reason == BlockReason.IO:
            # Duración aleatoria 3–10 ticks
            self.running.io_remaining = self._rnd.randint(3, 10)
        self.blocked.append(self.running)
        self.running = None
        return True

    def pause_running(self):
        return self.block_running(BlockReason.PAUSED)

    def unblock_pid(self, pid: int) -> bool:
        # Desbloquear si está en bloqueados (I/O/DEPENDENCY/PAUSED)
        for p in list(self.blocked):
            if p.pid == pid:
                self.blocked.remove(p)
                p.block_reason = None
                p.waiting_for_pid = None
                p.io_remaining = 0
                p.set_state(ProcessState.READY)
                self.ready.append(p)
                return True
        return False

    def _finish_running(self):
        if not self.running:
            return
        if self.repeat_mode:
            self.running.remaining_time = self.running.burst_time
            self.running.set_state(ProcessState.READY)
            self.ready.append(self.running)
        else:
            done_pid = self.running.pid
            if self.simulate_zombie:
                self.running.set_state(ProcessState.ZOMBIE)
                self.zombies.append(self.running)
                self._orphan_dependents(done_pid)
            else:
                self.running.set_state(ProcessState.FINISHED)
                self.finished.append(self.running)
                self._orphan_dependents(done_pid)
        self.running = None

    def revive_for_cycle(self, include_zombies: bool=False):
        revived = 0
        for p in list(self.finished):
            self.finished.remove(p)
            p.remaining_time = p.burst_time
            p.set_state(ProcessState.READY)
            self.ready.append(p)
            revived += 1
        if include_zombies:
            for p in list(self.zombies):
                self.zombies.remove(p)
                p.remaining_time = p.burst_time
                p.set_state(ProcessState.READY)
                self.ready.append(p)
                revived += 1
        return revived

    def finalize_pid(self, pid: int) -> bool:
        def finish_to_state(proc: Process):
            if self.simulate_zombie:
                proc.set_state(ProcessState.ZOMBIE); self.zombies.append(proc)
            else:
                proc.set_state(ProcessState.FINISHED); self.finished.append(proc)

        if self.running and self.running.pid == pid:
            finish_to_state(self.running)
            self._orphan_dependents(pid)
            self.running = None
            return True

        for p in list(self.ready):
            if p.pid == pid:
                self.ready.remove(p); finish_to_state(p); self._orphan_dependents(pid); return True
        for p in list(self.blocked):
            if p.pid == pid:
                self.blocked.remove(p); p.block_reason=None; p.waiting_for_pid=None; p.io_remaining=0; finish_to_state(p); self._orphan_dependents(pid); return True
        for p in list(self.zombies):
            if p.pid == pid:
                self.zombies.remove(p); p.set_state(ProcessState.FINISHED); self.finished.append(p); return True
        for p in list(self.finished):
            if p.pid == pid:
                self.finished.remove(p); finish_to_state(p); self._orphan_dependents(pid); return True
        return False

    # Dependencias
    def depend_on(self, caller_pid: int, callee_pid: int):
        p = self.get_proc(caller_pid)
        if not p:
            return False
        p.block_reason = BlockReason.DEPENDENCY
        p.waiting_for_pid = callee_pid
        if self.running and self.running.pid == caller_pid:
            self.block_running(BlockReason.DEPENDENCY)
        else:
            try:
                self.ready.remove(p)
            except ValueError:
                pass
            p.set_state(ProcessState.BLOCKED)
            self.blocked.append(p)
        return True

    def reply(self, from_pid: int, to_pid: int, msg: str = "OK"):
        self.mailboxes[to_pid].append((from_pid, msg, self.time))

    def _unblock_by_replies(self):
        if not self.blocked:
            return
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid is not None:
                inbox = self.mailboxes.get(p.pid, [])
                idx = next((i for i,(src,_m,_t) in enumerate(inbox) if src == p.waiting_for_pid), None)
                if idx is not None:
                    inbox.pop(idx)
                    p.block_reason = None
                    p.waiting_for_pid = None
                    p.set_state(ProcessState.READY)
                    self.blocked.remove(p)
                    self.ready.append(p)
    def _unblock_dependents_of(self, callee_pid: int):
        """Auto: si el PID 'callee_pid' está ejecutándose, libera a los procesos
        que dependen de él (espera-respuesta inmediata al menos un tick de CPU)."""
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid == callee_pid:
                self.blocked.remove(p)
                p.block_reason = None
                p.waiting_for_pid = None
                p.set_state(ProcessState.READY)
                self.ready.append(p)


    def reap_zombies(self):
        for p in list(self.zombies):
            p.set_state(ProcessState.FINISHED)
            self.zombies.remove(p)
            self.finished.append(p)

    def reset(self, keep_options: bool=True):
        simz = self.simulate_zombie if keep_options else False
        rep = self.repeat_mode if keep_options else True
        self.__init__(simulate_zombie=simz, repeat_mode=rep)

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Simulador — Vista Única (FCFS + Dependencias + Control manual)")
        self.scheduler = Scheduler(simulate_zombie=False, repeat_mode=True)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.on_tick)
        self.init_ui()

    def init_ui(self):
        root = QWidget()
        self.setCentralWidget(root)
        self.setMinimumSize(1100, 600)

        # Labels
        self.lbl_time = QLabel("Tiempo: 0")
        self.lbl_running = QLabel("RUNNING: -")

        # Header bar (top-right icon button)
        header_bar = QHBoxLayout()
        header_bar.addStretch(1)
        self.btn_toggle_view = QToolButton()
        self.btn_toggle_view.setCheckable(True)
        self.btn_toggle_view.setAutoRaise(True)
        self.btn_toggle_view.setFixedSize(26, 26)
        self.btn_toggle_view.setIconSize(QSize(18, 18))
        self.btn_toggle_view.setToolTip("Alternar vista por estados")
        self.btn_toggle_view.setIcon(self.style().standardIcon(QStyle.SP_FileDialogListView))
        self.btn_toggle_view.setStyleSheet(
            "QToolButton { border: none; border-radius: 6px; padding: 2px; }"
            "QToolButton:checked { background-color: #3b82f6; }"
        )
        self.btn_toggle_view.toggled.connect(self.on_toggle_view)
        header_bar.addWidget(self.btn_toggle_view)

        # Buttons
        self.btn_add = QPushButton("Agregar proceso")
        self.btn_add5 = QPushButton("Agregar 5 demo")
        self.btn_start = QPushButton("▶ Iniciar")
        self.btn_pause = QPushButton("⏸ Pausar reloj")
        self.btn_step = QPushButton("⏭ Paso +1 tick")
        self.btn_block = QPushButton("Bloquear RUNNING (I/O)")
        self.btn_pause_proc = QPushButton("Pausar RUNNING (manual)")
        self.btn_unblock = QPushButton("Reanudar/Desbloquear seleccionado")
        self.btn_reap = QPushButton("Reap Zombis")
        self.btn_reset = QPushButton("Reiniciar")

        self.cmb_speed = QComboBox()
        for ms in [100, 200, 400, 800]:
            self.cmb_speed.addItem(f"{ms} ms/tick", ms)
        self.cmb_speed.setCurrentIndex(0)

        # Checkboxes
        self.chk_zombie = QCheckBox("Simular estado Zombi")
        self.chk_auto_arrivals = QCheckBox("Llegadas automáticas")
        self.chk_auto_blocks = QCheckBox("Bloqueos aleatorios")
        self.chk_repeat = QCheckBox("Modo repetición (ciclar procesos)")
        self.chk_repeat.setChecked(True)

        # Dependencias
        self.spn_target = QSpinBox()
        self.spn_target.setWrapping(False)
        self.spn_target.setRange(1, 9999)
        self.spn_target.setPrefix("PID objetivo: ")
        self.btn_depend = QPushButton("Depender (RUNNING espera a PID)")
        self.btn_reply = QPushButton("Responder (RUNNING → PID objetivo)")
        self.btn_finalize = QPushButton("Finalizar (PID objetivo)")

        # Conexiones
        self.btn_add.clicked.connect(self.on_add)
        self.btn_add5.clicked.connect(self.on_add5)
        self.btn_start.clicked.connect(self.on_start)
        self.btn_pause.clicked.connect(self.on_pause_clock)
        self.btn_step.clicked.connect(self.on_step)
        self.btn_block.clicked.connect(self.on_block_io)
        self.btn_pause_proc.clicked.connect(self.on_pause_proc)
        self.btn_unblock.clicked.connect(self.on_unblock_selected)
        self.btn_reap.clicked.connect(self.on_reap)
        self.btn_reset.clicked.connect(self.on_reset)
        self.cmb_speed.currentIndexChanged.connect(self.on_speed_changed)
        self.chk_zombie.stateChanged.connect(self.on_toggle_zombie)
        self.chk_auto_arrivals.stateChanged.connect(self.on_toggle_auto_arrivals)
        self.chk_auto_blocks.stateChanged.connect(self.on_toggle_auto_blocks)
        self.chk_repeat.stateChanged.connect(self.on_toggle_repeat)
        self.btn_depend.clicked.connect(self.on_depend)
        self.btn_reply.clicked.connect(self.on_reply)
        self.btn_finalize.clicked.connect(self.on_finalize)

        # Botones tamaños
        for b in [self.btn_add, self.btn_add5, self.btn_start, self.btn_pause, self.btn_step,
                  self.btn_block, self.btn_pause_proc, self.btn_unblock, self.btn_depend,
                  self.btn_reply, self.btn_finalize, self.btn_reap, self.btn_reset]:
            b.setMinimumHeight(32)
            b.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Panel controles
        controls_layout = QVBoxLayout()
        controls_layout.addLayout(header_bar)
        controls_layout.addWidget(self.lbl_time)
        controls_layout.addWidget(self.lbl_running)
        controls_layout.addWidget(self.cmb_speed)
        controls_layout.addWidget(self.chk_zombie)
        controls_layout.addWidget(self.chk_auto_arrivals)
        controls_layout.addWidget(self.chk_auto_blocks)
        controls_layout.addWidget(self.chk_repeat)
        controls_layout.addWidget(self.btn_add)
        controls_layout.addWidget(self.btn_add5)
        controls_layout.addWidget(self.btn_start)
        controls_layout.addWidget(self.btn_pause)
        controls_layout.addWidget(self.btn_step)
        controls_layout.addWidget(self.btn_block)
        controls_layout.addWidget(self.btn_pause_proc)
        controls_layout.addWidget(self.btn_unblock)

        manual_box = QGroupBox("Control manual de Procesos")
        vb = QVBoxLayout()
        vb.addWidget(self.spn_target)
        vb.addWidget(self.btn_depend)
        vb.addWidget(self.btn_reply)
        vb.addWidget(self.btn_finalize)
        manual_box.setLayout(vb)

        controls_layout.addWidget(manual_box)
        controls_layout.addWidget(self.btn_reap)
        controls_layout.addWidget(self.btn_reset)
        controls_layout.addStretch(1)

        controls_box = QGroupBox("Controles")
        controls_box.setLayout(controls_layout)
        controls_container = QWidget()
        vwrap = QVBoxLayout(controls_container)
        vwrap.addWidget(controls_box)
        vwrap.setContentsMargins(0,0,0,0)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(controls_container)
        scroll.setMinimumWidth(330)
        scroll.setMaximumWidth(390)

        # Tabla única
        self.tbl_all = QTableWidget(0, 5)
        self.tbl_all.setHorizontalHeaderLabels(["PID","Estado","Ráfaga restante","Razón","Esperando PID"])
        self.tbl_all.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)

        processes_box = QGroupBox("Procesos")
        pv = QVBoxLayout()

        # Contenedores de vista
        self.unified_container = QWidget()
        uvl = QVBoxLayout(self.unified_container)
        uvl.setContentsMargins(0,0,0,0)
        uvl.addWidget(self.tbl_all)

        self.grouped_container = QWidget()
        gvl = QVBoxLayout(self.grouped_container)
        gvl.setContentsMargins(0,0,0,0)

        # RUNNING + READY
        self.tbl_ready = QTableWidget(0, 5)
        self.tbl_ready.setHorizontalHeaderLabels(["PID","Estado","Ráfaga restante","Razón","Esperando PID"])
        self.tbl_ready.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_rr = QGroupBox("RUNNING + READY")
        lay_rr = QVBoxLayout(); lay_rr.addWidget(self.tbl_ready); box_rr.setLayout(lay_rr)
        gvl.addWidget(box_rr)

        # BLOCKED + PAUSED
        self.tbl_blocked = QTableWidget(0, 5)
        self.tbl_blocked.setHorizontalHeaderLabels(["PID","Estado","Ráfaga restante","Razón","Esperando PID"])
        self.tbl_blocked.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_bp = QGroupBox("BLOCKED + PAUSED")
        lay_bp = QVBoxLayout(); lay_bp.addWidget(self.tbl_blocked); box_bp.setLayout(lay_bp)
        gvl.addWidget(box_bp)

        # FINISHED + ZOMBIE
        self.tbl_done = QTableWidget(0, 5)
        self.tbl_done.setHorizontalHeaderLabels(["PID","Estado","Ráfaga restante","Razón","Esperando PID"])
        self.tbl_done.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_dz = QGroupBox("FINISHED + ZOMBIE")
        lay_dz = QVBoxLayout(); lay_dz.addWidget(self.tbl_done); box_dz.setLayout(lay_dz)
        gvl.addWidget(box_dz)

        # Por defecto, tabla unificada
        self.grouped_container.hide()
        pv.addWidget(self.unified_container)
        pv.addWidget(self.grouped_container)
        processes_box.setLayout(pv)

        layout = QHBoxLayout()
        layout.addWidget(scroll, 0)
        layout.addWidget(processes_box, 1)
        root.setLayout(layout)

        self.update_pid_spin_range()
        self.refresh_table_all()

    # Utilidad UI
    def update_labels(self):
        self.lbl_time.setText(f"Tiempo: {self.scheduler.time}")
        if self.scheduler.running:
            self.lbl_running.setText(f"RUNNING: PID {self.scheduler.running.pid} (restante={self.scheduler.running.remaining_time})")
        else:
            self.lbl_running.setText("RUNNING: -")

    def update_pid_spin_range(self):
        max_pid = max(1, self.scheduler.next_pid - 1)
        self.spn_target.setRange(1, max_pid)
        if self.spn_target.value() > max_pid:
            self.spn_target.setValue(max_pid)

    # --- Handlers ---
    def on_add(self):
        burst = random.randint(3, 10)
        self.scheduler.create_process(burst)
        self.scheduler.admit_all_new()
        if self.scheduler.running is None:
            self.scheduler.running = self.scheduler.choose_next()
        self.update_pid_spin_range()
        self.refresh_current_view()

    def on_add5(self):
        for _ in range(5):
            self.on_add()

    def on_start(self):
        # Inyección si sistema vacío y llegadas automáticas ON
        if self.chk_auto_arrivals.isChecked() and self.scheduler.system_empty():
            self.scheduler.create_process(burst=random.randint(3,10))
            self.scheduler.admit_all_new()
        # Sincronizar repeat con casilla
        self.scheduler.repeat_mode = self.chk_repeat.isChecked()
        if not self.timer.isActive():
            self.timer.start(self.cmb_speed.currentData())
        self.refresh_current_view()

    def on_pause_clock(self):
        self.timer.stop()

    def on_step(self):
        if self.timer.isActive():
            self.timer.stop()
        self.on_tick()

    def on_block_io(self):
        self.scheduler.block_running(BlockReason.IO)
        self.refresh_current_view()

    def on_pause_proc(self):
        self.scheduler.pause_running()
        self.refresh_current_view()

    def on_unblock_selected(self):
        # Usar PID objetivo para desbloquear
        pid = self.spn_target.value()
        if not self.scheduler.unblock_pid(pid):
            QMessageBox.information(self, "Info", f"PID {pid} no está en estado bloqueado/pausado/dependiendo.")
        self.refresh_current_view()

    def on_reap(self):
        self.scheduler.reap_zombies()
        self.refresh_current_view()

    def on_reset(self):
        self.timer.stop()
        self.scheduler.reset(keep_options=True)
        self.update_pid_spin_range()
        self.refresh_current_view()

    def on_speed_changed(self, _):
        if self.timer.isActive():
            self.timer.start(self.cmb_speed.currentData())

    def on_toggle_zombie(self, _state):
        self.scheduler.simulate_zombie = self.chk_zombie.isChecked()

    def on_toggle_auto_arrivals(self, _state):
        pass  # lógica ya se aplica en tick/start

    def on_toggle_auto_blocks(self, _state):
        pass

    def on_toggle_repeat(self, _state):
        checked = self.chk_repeat.isChecked()
        self.scheduler.repeat_mode = checked
        if checked:
            # Revivir todos los FINISHED y ZOMBIE a READY para reanudar el ciclo
            self.scheduler.revive_for_cycle(include_zombies=True)
        self.refresh_current_view()

    def on_depend(self):
        if not self.scheduler.running:
            QMessageBox.information(self, "Info", "No hay proceso RUNNING para establecer dependencia.")
            return
        callee = self.spn_target.value()
        caller = self.scheduler.running.pid
        if caller == callee:
            QMessageBox.warning(self, "Aviso", "Un proceso no puede depender de sí mismo.")
            return
        ok = self.scheduler.depend_on(caller_pid=caller, callee_pid=callee)
        if not ok:
            QMessageBox.warning(self, "Aviso", "No se pudo establecer la dependencia.")
        self.refresh_current_view()

    def on_finalize(self):
        pid = self.spn_target.value()
        if not self.scheduler.finalize_pid(pid):
            QMessageBox.information(self, "Info", f"No se encontró el PID {pid} activo.")
        self.refresh_current_view()

    def on_reply(self):
        if not self.scheduler.running:
            QMessageBox.information(self, "Info", "No hay proceso RUNNING para responder.")
            return
        to_pid = self.spn_target.value()
        self.scheduler.reply(from_pid=self.scheduler.running.pid, to_pid=to_pid, msg="OK")
        self.refresh_current_view()

    def on_tick(self):
        # Leer flags desde checkboxes
        self.scheduler.simulate_zombie = self.chk_zombie.isChecked()
        self.scheduler.repeat_mode = self.chk_repeat.isChecked()
        auto_arrivals = self.chk_auto_arrivals.isChecked()
        auto_blocks = self.chk_auto_blocks.isChecked()

        self.scheduler.tick(auto_arrivals=auto_arrivals, auto_blocks=auto_blocks)
        self.update_pid_spin_range()
        self.refresh_current_view()

    def on_toggle_view(self, checked: bool):
        self.btn_toggle_view.setIcon(self.style().standardIcon(QStyle.SP_FileDialogDetailedView if checked else QStyle.SP_FileDialogListView))
        if checked:
            self.unified_container.hide()
            self.grouped_container.show()
            self.refresh_tables_grouped()
        else:
            self.grouped_container.hide()
            self.unified_container.show()
            self.refresh_table_all()

    # --- Vistas ---
    def refresh_current_view(self):
        self.update_labels()
        if self.btn_toggle_view.isChecked():
            self.refresh_tables_grouped()
        else:
            self.refresh_table_all()

    # Tabla separada en 3
    def refresh_tables_grouped(self):
        pro_running = [self.scheduler.running] if self.scheduler.running else []
        pro_ready = list(self.scheduler.ready)
        pro_blocked = [p for p in self.scheduler.blocked if p.block_reason in (BlockReason.IO, BlockReason.DEPENDENCY)]
        pro_paused = [p for p in self.scheduler.blocked if p.block_reason == BlockReason.PAUSED]
        pro_finished = list(self.scheduler.finished)
        pro_zombie = list(self.scheduler.zombies)

        def fill(tbl, items):
            tbl.setRowCount(len(items))
            for r, p in enumerate(items):
                reason = p.block_reason.name if p.block_reason else ""
                if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                    reason += f" ({p.io_remaining})"
                waitfor = str(p.waiting_for_pid) if p.waiting_for_pid is not None else ""
                cells = [str(p.pid), p.state.name, str(p.remaining_time), reason, waitfor]
                for c, val in enumerate(cells):
                    tbl.setItem(r, c, QTableWidgetItem(val))
                color = STATE_COLORS.get(p.state)
                for c in range(5):
                    tbl.item(r, c).setBackground(color)

        fill(self.tbl_ready, [*pro_running, *pro_ready])
        fill(self.tbl_blocked, [*pro_blocked, *pro_paused])
        fill(self.tbl_done, [*pro_finished, *pro_zombie])

    # Tabla única
    def refresh_table_all(self):
        procs: List[Process] = []
        if self.scheduler.running: procs.append(self.scheduler.running)
        procs += list(self.scheduler.ready)
        procs += list(self.scheduler.blocked)
        procs += list(self.scheduler.zombies)
        procs += list(self.scheduler.finished)
        procs += list(self.scheduler.new)

        self.tbl_all.setRowCount(len(procs))
        for r, p in enumerate(procs):
            reason = p.block_reason.name if p.block_reason else ""
            if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                reason += f" ({p.io_remaining})"
            waitfor = str(p.waiting_for_pid) if p.waiting_for_pid is not None else ""
            cells = [str(p.pid), p.state.name, str(p.remaining_time), reason, waitfor]
            for c, val in enumerate(cells):
                self.tbl_all.setItem(r, c, QTableWidgetItem(val))
            color = STATE_COLORS.get(p.state)
            for c in range(5):
                self.tbl_all.item(r, c).setBackground(color)

def main():
    import sys
    app = QApplication(sys.argv)
    w = MainWindow()
    w.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
