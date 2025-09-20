# -*- coding: utf-8 -*-
"""
Simulador — Vista Única (FCFS + Dependencias + Control manual + Prioridades)
----------------------------------------------------------------------------

Cambios solicitados:
1) UI: Reemplazar el botón "Responder" por un selector (QComboBox) para
   cambiar la PRIORIDAD del "PID objetivo" (Alta / Media / Baja) +
   botón "Aplicar prioridad al PID".
2) Tablas: Columna "Prioridad" para ver la prioridad de cada proceso.
3) Planificación con prioridades SIN hambruna (no starvation):
   - Se usa **Weighted Round-Robin por CLASE de prioridad** (WRR):
       Orden de clases: [Alta, Media, Baja]
       Pesos de clase (cuántas *veces* seguidas se sirve cada clase por ciclo):
           Alta: 2,  Media: 1,  Baja: 1
     Esto garantiza que, aunque existan procesos de Alta, **siempre** habrá huecos
     para que Media y Baja reciban CPU (evita que la Alta los bloquee indefinidamente).
   - Dentro de cada clase se mantiene **FIFO** (estilo cola) para escoger procesos.
   - Se mantiene un **quantum por prioridad por PROCESO** (preempción suave)
     para que Alta obtenga más ticks que Media y ésta más que Baja:
         Alta=3 ticks, Media=2 ticks, Baja=1 tick.

      => Combinación WRR (por clase) + Quantum (por proceso) produce:
         - Alta corre más seguido (y por más ticks cada vez), *pero*
           Media y Baja SIEMPRE obtendrán oportunidades de ejecución.
4) Se mantienen TODAS las funcionalidades existentes: dependencias, I/O aleatorio,
   modo repetición, zombis, etc.

El código incluye COMENTARIOS en cada sección clave para entender la lógica.
"""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum, auto
from typing import Optional, Deque, List, Dict, Tuple
from collections import deque, defaultdict
import random

from PySide6.QtCore import QTimer, QSize
from PySide6.QtGui import QColor
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QPushButton, QTableWidget, QTableWidgetItem,
    QHeaderView, QVBoxLayout, QHBoxLayout, QGroupBox, QMessageBox, QComboBox, QCheckBox, QSpinBox,
    QSizePolicy, QScrollArea, QToolButton, QStyle
)

# ----------------------------
#  Definiciones de enumerados
# ----------------------------

class ProcessState(Enum):
    NEW = auto()      # Aún no admitido a READY
    READY = auto()    # En cola para ejecutar
    RUNNING = auto()  # En CPU
    BLOCKED = auto()  # Bloqueado (I/O o dependencia)
    PAUSED = auto()   # Pausado manualmente (tratado como bloqueado)
    FINISHED = auto() # Finalizado (si repeat_mode=False)
    ZOMBIE = auto()   # Zombi (si simulate_zombie=True al finalizar)

class BlockReason(Enum):
    IO = auto()          # Esperando I/O (con temporizador)
    DEPENDENCY = auto()  # Esperando a otro PID
    PAUSED = auto()      # Pausa manual

class Priority(Enum):
    HIGH = auto()
    MEDIUM = auto()
    LOW = auto()

# Etiquetas bonitas para UI
PRIO_LABEL = {Priority.HIGH: "Alta", Priority.MEDIUM: "Media", Priority.LOW: "Baja"}

# Quantum de TICKS por PROCESO según prioridad (preempción suave)
#   Alta recibe 3 ticks seguidos, Media 2, Baja 1
PRIO_QUANTUM = {Priority.HIGH: 3, Priority.MEDIUM: 2, Priority.LOW: 1}

# Colores de la tabla por estado (solo UI)
STATE_COLORS = {
    ProcessState.NEW: QColor(66, 135, 245),
    ProcessState.READY: QColor(245, 211, 66),
    ProcessState.RUNNING: QColor(82, 196, 26),
    ProcessState.BLOCKED: QColor(255, 159, 28),
    ProcessState.PAUSED: QColor(128, 90, 213),
    ProcessState.FINISHED: QColor(120, 120, 120),
    ProcessState.ZOMBIE: QColor(220, 38, 38),
}

# ----------------------------
#  Modelo de Proceso
# ----------------------------
@dataclass
class Process:
    pid: int
    arrival_time: int
    burst_time: int
    remaining_time: int
    state: ProcessState = ProcessState.NEW
    block_reason: Optional[BlockReason] = None
    waiting_for_pid: Optional[int] = None
    io_remaining: int = 0          # ticks restantes en I/O (si aplica)
    priority: Priority = Priority.MEDIUM  # por defecto MEDIA

    def set_state(self, st: ProcessState):
        self.state = st

# ----------------------------
#  Planificador (Scheduler)
# ----------------------------
class Scheduler:
    # Pesos de la política Weighted Round-Robin por CLASE de prioridad
    #   Secuencia de clases en un "ciclo": Alta x2, Media x1, Baja x1 (si hay candidatos)
    WRR_WEIGHTS = {Priority.HIGH: 2, Priority.MEDIUM: 2, Priority.LOW: 1}
    PRIO_CYCLE = [Priority.HIGH, Priority.MEDIUM, Priority.LOW]

    def __init__(self, simulate_zombie: bool = False, repeat_mode: bool = True):
        # Reloj simulado
        self.time: int = 0

        # PID incremental
        self.next_pid: int = 1

        # Flags de comportamiento
        self.simulate_zombie = simulate_zombie
        self.repeat_mode = repeat_mode

        # Conjuntos por estado
        self.new: List[Process] = []
        self.ready: Deque[Process] = deque()
        self.blocked: List[Process] = []
        self.finished: List[Process] = []
        self.zombies: List[Process] = []
        self.running: Optional[Process] = None

        # Utilidades
        self._rnd = random.Random()
        self.mailboxes: Dict[int, List[Tuple[int, str, int]]] = defaultdict(list)
        self._spawned_when_empty = False  # para llegadas automáticas (solo 1 vez en vacío)

        # Control de quantum usado por el RUNNING actual (para preempción)
        self._quantum_used: int = 0

        # Estado del Round-Robin por clases de prioridad (evita hambruna)
        self._wrr_idx: int = 0  # índice dentro de PRIO_CYCLE
        # presupuesto (cuántas elecciones seguidas puede hacer la clase actual antes de girar)
        self._wrr_budget: int = self.WRR_WEIGHTS[self.PRIO_CYCLE[self._wrr_idx]]

    # ----- Utilidades de consulta -----
    def system_empty(self) -> bool:
        """True si no hay NEW, READY ni RUNNING (útil para llegadas automáticas)."""
        return not (self.new or self.ready or self.running)

    def get_proc(self, pid: int) -> Optional[Process]:
        """Busca un proceso por PID en cualquier lista activa."""
        if self.running and self.running.pid == pid:
            return self.running
        for lst in (self.ready, self.blocked, self.new, self.finished, self.zombies):
            for p in lst:
                if p.pid == pid:
                    return p
        return None

    # ----- Gestión de procesos -----
    def create_process(self, burst: int) -> Process:
        """Crea un proceso en estado NEW (se admitirá a READY en el siguiente admit_all_new)."""
        p = Process(pid=self.next_pid, arrival_time=self.time, burst_time=burst, remaining_time=burst)
        self.next_pid += 1
        self.new.append(p)
        return p

    def set_priority(self, pid: int, prio: Priority) -> bool:
        """Cambia la prioridad de un proceso (si es RUNNING, reinicia su conteo de quantum)."""
        p = self.get_proc(pid)
        if not p:
            return False
        p.priority = prio
        if self.running and self.running.pid == pid:
            self._quantum_used = 0
        return True

    def admit_all_new(self):
        """Mueve todos los NEW a READY (admisión)."""
        for p in list(self.new):
            p.set_state(ProcessState.READY)
            self.ready.append(p)
            self.new.remove(p)

    # ----- Weighted Round-Robin por CLASE de prioridad -----
    def _advance_wrr(self):
        """Pasa a la siguiente CLASE de prioridad en el ciclo y recarga su presupuesto."""
        self._wrr_idx = (self._wrr_idx + 1) % len(self.PRIO_CYCLE)
        self._wrr_budget = self.WRR_WEIGHTS[self.PRIO_CYCLE[self._wrr_idx]]

    def _pop_ready_by_priority(self, prio: Priority) -> Optional[Process]:
        """Extrae (y devuelve) el PRIMER proceso READY con la prioridad dada (FIFO dentro de la clase)."""
        for idx, cand in enumerate(self.ready):
            if cand.priority == prio:
                if idx == 0:
                    return self.ready.popleft()
                # remover por índice manteniendo orden del resto
                tmp = []
                for _ in range(idx):
                    tmp.append(self.ready.popleft())
                p = self.ready.popleft()
                for it in reversed(tmp):
                    self.ready.appendleft(it)
                return p
        return None

    def choose_next(self) -> Optional[Process]:
        """
        Selecciona el próximo RUNNING usando WRR por CLASE de prioridad:
        - Se intenta servir a la CLASE actual mientras tenga presupuesto y existan candidatos.
        - Si no hay candidatos en esa CLASE o agotó presupuesto, se avanza a la siguiente CLASE.
        - Esto asegura que Media y Baja SIEMPRE obtendrán CPU si existen.
        """
        if not self.ready:
            return None

        attempts = 0
        max_attempts = len(self.PRIO_CYCLE) * (max(self.WRR_WEIGHTS.values()) + 1)

        while attempts < max_attempts:
            current_class = self.PRIO_CYCLE[self._wrr_idx]

            # Si no hay candidatos de la clase actual, saltamos a la siguiente
            has_candidate = any(p.priority == current_class for p in self.ready)
            if not has_candidate or self._wrr_budget <= 0:
                self._advance_wrr()
                attempts += 1
                continue

            # Extraemos el primer READY de esa clase (FIFO) y consumimos presupuesto
            p = self._pop_ready_by_priority(current_class)
            if p is None:
                self._advance_wrr()
                attempts += 1
                continue

            self._wrr_budget -= 1
            p.set_state(ProcessState.RUNNING)
            self._quantum_used = 0
            return p

        # Fallback: si algo fallara en el ciclo, tomar el primero de READY
        p = self.ready.popleft()
        p.set_state(ProcessState.RUNNING)
        self._quantum_used = 0
        return p

    # ----- Dependencias / Zombis -----
    def _orphan_dependents(self, callee_pid: int):
        """Los que esperan a callee_pid pasan a ZOMBIE si así se simula orfandad."""
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid == callee_pid:
                self.blocked.remove(p)
                p.block_reason = None
                p.waiting_for_pid = None
                p.set_state(ProcessState.ZOMBIE)
                self.zombies.append(p)

    # ----- Preempción por quantum -----
    def _preempt_running_if_needed(self):
        """Si el RUNNING agotó su quantum y hay READY, se reencola y se deja elegir a otro."""
        if not self.running:
            return
        max_q = PRIO_QUANTUM[self.running.priority]
        if self._quantum_used >= max_q and len(self.ready) > 0:
            # Reencolar al final (manteniendo FIFO dentro de su clase)
            self.running.set_state(ProcessState.READY)
            self.running.block_reason = None
            self.running.waiting_for_pid = None
            self.running.io_remaining = 0
            self.ready.append(self.running)
            self.running = None  # quedamos listos para elegir otro en este mismo tick

    # ----- Avance de 1 tick del reloj (núcleo del simulador) -----
    def tick(self, auto_arrivals: bool, auto_blocks: bool):
        """Simula 1 'tick': llegadas, desbloqueos, despacho, ejecución/preempción, etc."""
        # 1) Avanza el reloj
        self.time += 1

        # 2) Llegadas automáticas
        if auto_arrivals:
            active = (1 if self.running else 0) + len(self.ready) + len(self.blocked)
            if active > 0:
                if self._rnd.random() < 0.05:  # 5% de probabilidad por tick
                    self.create_process(burst=self._rnd.randint(3, 10))
                self._spawned_when_empty = False
            else:
                # Si el sistema está "vacío", inyectar 1 proceso una sola vez
                if not self._spawned_when_empty:
                    self.create_process(burst=self._rnd.randint(3, 10))
                    self._spawned_when_empty = True

        # 3) Admitir todos los NEW a READY
        self.admit_all_new()

        # 4) Desbloqueos por I/O (disminuye el temporizador)
        for p in list(self.blocked):
            if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                p.io_remaining -= 1
                if p.io_remaining <= 0:
                    p.block_reason = None
                    p.set_state(ProcessState.READY)
                    self.blocked.remove(p)
                    self.ready.append(p)

        # 5) Desbloqueos por respuesta a dependencia
        self._unblock_by_replies()

        # 6) Si está el modo repetición y no hay READY ni RUNNING, revivir para ciclar
        if self.repeat_mode and (not self.ready and self.running is None) and (self.finished or self.zombies):
            self.revive_for_cycle(include_zombies=True)

        # 7) Si no hay RUNNING, seleccionar uno usando WRR por clase de prioridad
        if self.running is None:
            self.running = self.choose_next()

        # 8) Ejecutar el RUNNING (si existe) o simular bloqueos aleatorios
        if self.running:
            # Al menos 1 tick del callee desbloquea dependientes "esperando respuesta"
            self._unblock_dependents_of(self.running.pid)

            # Opción de bloquearlo aleatoriamente por I/O
            if auto_blocks and self._rnd.random() < 0.04:  # 4% por tick
                self.block_running(BlockReason.IO)
            else:
                # Consume 1 tick de CPU del RUNNING
                self.running.remaining_time -= 1
                self._quantum_used += 1

                # Si terminó su ráfaga
                if self.running.remaining_time <= 0:
                    self._finish_running()
                else:
                    # Si agotó su quantum, permitir que otro entre (preempción suave)
                    self._preempt_running_if_needed()

    # ----- Operaciones de bloqueo/pausa -----
    def block_running(self, reason: BlockReason):
        """Bloquea el RUNNING actual (I/O, dependencia o pausa manual)."""
        if not self.running:
            return False
        self.running.set_state(ProcessState.PAUSED if reason == BlockReason.PAUSED else ProcessState.BLOCKED)
        self.running.block_reason = reason
        if reason == BlockReason.IO:
            # Duración aleatoria 3–10 ticks
            self.running.io_remaining = self._rnd.randint(3, 10)
        self.blocked.append(self.running)
        self.running = None
        return True

    def pause_running(self):
        """Atajo para pausar manualmente el RUNNING."""
        return self.block_running(BlockReason.PAUSED)

    def unblock_pid(self, pid: int) -> bool:
        """Mueve un PID desde bloqueados/pausados a READY (si aplica)."""
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

    # ----- Finalización de RUNNING y modo repetición / zombis -----
    def _finish_running(self):
        """Acción al terminar un RUNNING su ráfaga (o al forzar finalizar)."""
        if not self.running:
            return
        if self.repeat_mode:
            # En modo repetición, el proceso vuelve con su ráfaga restaurada
            self.running.remaining_time = self.running.burst_time
            self.running.set_state(ProcessState.READY)
            self.ready.append(self.running)
        else:
            # En modo normal, puede ir a FINISHED o ZOMBIE (según flag)
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

    def revive_for_cycle(self, include_zombies: bool = False):
        """Revive FINISHED (y ZOMBIE si include_zombies) a READY para 'ciclar'."""
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
        """Finaliza forzosamente un PID (respetando simulate_zombie y órfandad)."""
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
                self.blocked.remove(p); p.block_reason=None; p.waiting_for_pid=None; p.io_remaining=0
                finish_to_state(p); self._orphan_dependents(pid); return True
        for p in list(self.zombies):
            if p.pid == pid:
                self.zombies.remove(p); p.set_state(ProcessState.FINISHED); self.finished.append(p); return True
        for p in list(self.finished):
            if p.pid == pid:
                self.finished.remove(p); finish_to_state(p); self._orphan_dependents(pid); return True
        return False

    # ----- Dependencias (espera-respuesta) -----
    def depend_on(self, caller_pid: int, callee_pid: int):
        """Hace que 'caller' dependa de 'callee' (bloquea hasta recibir respuesta / tick del callee)."""
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
        """No usada por la UI actual: cola un 'mensaje' al PID 'to_pid' para desbloqueo por dependencia."""
        self.mailboxes[to_pid].append((from_pid, msg, self.time))

    def _unblock_by_replies(self):
        """Desbloquea procesos en dependencia cuando reciben respuesta en 'mailboxes'."""
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
        """Auto-desbloqueo: si 'callee_pid' ejecuta al menos 1 tick, libera a los que dependían de él."""
        for p in list(self.blocked):
            if p.block_reason == BlockReason.DEPENDENCY and p.waiting_for_pid == callee_pid:
                self.blocked.remove(p)
                p.block_reason = None
                p.waiting_for_pid = None
                p.set_state(ProcessState.READY)
                self.ready.append(p)

    # ----- Zombis -> Finished -----
    def reap_zombies(self):
        """Convierte todos los ZOMBIE en FINISHED (similar a 'wait()' en SO)."""
        for p in list(self.zombies):
            p.set_state(ProcessState.FINISHED)
            self.zombies.remove(p)
            self.finished.append(p)

    # ----- Reinicio del simulador -----
    def reset(self, keep_options: bool = True):
        """Reinicia todo; puede conservar flags simulate_zombie y repeat_mode."""
        simz = self.simulate_zombie if keep_options else False
        rep = self.repeat_mode if keep_options else True
        self.__init__(simulate_zombie=simz, repeat_mode=rep)

# ----------------------------
#  Ventana principal (Qt)
# ----------------------------
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Simulador — Vista Única (FCFS + Dependencias + Control manual + Prioridades)")
        self.scheduler = Scheduler(simulate_zombie=False, repeat_mode=True)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.on_tick)
        self.init_ui()

    # ----- Construcción de UI -----
    def init_ui(self):
        root = QWidget()
        self.setCentralWidget(root)
        self.setMinimumSize(1100, 600)

        # Indicadores superiores
        self.lbl_time = QLabel("Tiempo: 0")
        self.lbl_running = QLabel("RUNNING: -")

        # Botón para alternar vista (tabla única vs. dividida)
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

        # Controles principales
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

        # Velocidad (ms por tick)
        self.cmb_speed = QComboBox()
        for ms in [100, 200, 400, 800]:
            self.cmb_speed.addItem(f"{ms} ms/tick", ms)
        self.cmb_speed.setCurrentIndex(0)

        # Flags
        self.chk_zombie = QCheckBox("Simular estado Zombi")
        self.chk_auto_arrivals = QCheckBox("Llegadas automáticas")
        self.chk_auto_blocks = QCheckBox("Bloqueos aleatorios")
        self.chk_repeat = QCheckBox("Modo repetición (ciclar procesos)")
        self.chk_repeat.setChecked(True)

        # Control manual (dependencias + prioridad + finalizar)
        self.spn_target = QSpinBox()
        self.spn_target.setWrapping(False)
        self.spn_target.setRange(1, 9999)
        self.spn_target.setPrefix("PID objetivo: ")

        self.btn_depend = QPushButton("Depender (RUNNING espera a PID)")

        # Selector de prioridad y botón aplicar (reemplaza al viejo "Responder")
        self.cmb_priority = QComboBox()
        self.cmb_priority.addItems(["Alta", "Media", "Baja"])
        self.cmb_priority.setCurrentIndex(1)  # Media por defecto
        self.cmb_priority.setToolTip("Cambiar prioridad del PID objetivo")
        self.btn_apply_prio = QPushButton("Aplicar prioridad al PID")

        self.btn_finalize = QPushButton("Finalizar (PID objetivo)")

        # Conexiones de señales
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
        self.btn_apply_prio.clicked.connect(self.on_apply_priority)
        self.btn_finalize.clicked.connect(self.on_finalize)

        # Ajustes visuales de botones
        for b in [self.btn_add, self.btn_add5, self.btn_start, self.btn_pause, self.btn_step,
                  self.btn_block, self.btn_pause_proc, self.btn_unblock, self.btn_depend,
                  self.btn_apply_prio, self.btn_finalize, self.btn_reap, self.btn_reset]:
            b.setMinimumHeight(32)
            b.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Layout del panel izquierdo (controles)
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
        vb.addWidget(self.cmb_priority)
        vb.addWidget(self.btn_apply_prio)
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
        vwrap.setContentsMargins(0, 0, 0, 0)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(controls_container)
        scroll.setMinimumWidth(330)
        scroll.setMaximumWidth(390)

        # ---- Tablas de procesos ----
        headers = ["PID", "Estado", "Ráfaga restante", "Razón", "Esperando PID", "Prioridad"]

        # Tabla única
        self.tbl_all = QTableWidget(0, len(headers))
        self.tbl_all.setHorizontalHeaderLabels(headers)
        self.tbl_all.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)

        processes_box = QGroupBox("Procesos")
        pv = QVBoxLayout()

        # Contenedor de vista unificada
        self.unified_container = QWidget()
        uvl = QVBoxLayout(self.unified_container)
        uvl.setContentsMargins(0, 0, 0, 0)
        uvl.addWidget(self.tbl_all)

        # Contenedor de vista dividida por estados
        self.grouped_container = QWidget()
        gvl = QVBoxLayout(self.grouped_container)
        gvl.setContentsMargins(0, 0, 0, 0)

        # RUNNING + READY
        self.tbl_ready = QTableWidget(0, len(headers))
        self.tbl_ready.setHorizontalHeaderLabels(headers)
        self.tbl_ready.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_rr = QGroupBox("RUNNING + READY")
        lay_rr = QVBoxLayout(); lay_rr.addWidget(self.tbl_ready); box_rr.setLayout(lay_rr)
        gvl.addWidget(box_rr)

        # BLOCKED + PAUSED
        self.tbl_blocked = QTableWidget(0, len(headers))
        self.tbl_blocked.setHorizontalHeaderLabels(headers)
        self.tbl_blocked.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_bp = QGroupBox("BLOCKED + PAUSED")
        lay_bp = QVBoxLayout(); lay_bp.addWidget(self.tbl_blocked); box_bp.setLayout(lay_bp)
        gvl.addWidget(box_bp)

        # FINISHED + ZOMBIE
        self.tbl_done = QTableWidget(0, len(headers))
        self.tbl_done.setHorizontalHeaderLabels(headers)
        self.tbl_done.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        box_dz = QGroupBox("FINISHED + ZOMBIE")
        lay_dz = QVBoxLayout(); lay_dz.addWidget(self.tbl_done); box_dz.setLayout(lay_dz)
        gvl.addWidget(box_dz)

        # Por defecto se muestra la vista unificada
        self.grouped_container.hide()
        pv.addWidget(self.unified_container)
        pv.addWidget(self.grouped_container)
        processes_box.setLayout(pv)

        # Layout raíz
        layout = QHBoxLayout()
        layout.addWidget(scroll, 0)
        layout.addWidget(processes_box, 1)
        root.setLayout(layout)

        self.update_pid_spin_range()
        self.refresh_table_all()

    # ----- Utilidades de UI -----
    def update_labels(self):
        self.lbl_time.setText(f"Tiempo: {self.scheduler.time}")
        if self.scheduler.running:
            self.lbl_running.setText(
                f"RUNNING: PID {self.scheduler.running.pid} "
                f"(restante={self.scheduler.running.remaining_time}, "
                f"prio={PRIO_LABEL[self.scheduler.running.priority]})"
            )
        else:
            self.lbl_running.setText("RUNNING: -")

    def update_pid_spin_range(self):
        max_pid = max(1, self.scheduler.next_pid - 1)
        self.spn_target.setRange(1, max_pid)
        if self.spn_target.value() > max_pid:
            self.spn_target.setValue(max_pid)

    # ----- Handlers de eventos de UI -----
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
        # Si hay llegadas automáticas y el sistema está vacío, añadir uno para arrancar
        if self.chk_auto_arrivals.isChecked() and self.scheduler.system_empty():
            self.scheduler.create_process(burst=random.randint(3, 10))
            self.scheduler.admit_all_new()
        # Sincronizar el flag repeat con la UI
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
        pass

    def on_toggle_auto_blocks(self, _state):
        pass

    def on_toggle_repeat(self, _state):
        checked = self.chk_repeat.isChecked()
        self.scheduler.repeat_mode = checked
        if checked:
            # Revivir todos para continuar ciclo
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

    def on_apply_priority(self):
        pid = self.spn_target.value()
        text = self.cmb_priority.currentText()
        prio = Priority.MEDIUM
        if text == "Alta":
            prio = Priority.HIGH
        elif text == "Baja":
            prio = Priority.LOW

        if not self.scheduler.set_priority(pid, prio):
            QMessageBox.information(self, "Info", f"No se encontró el PID {pid} activo.")
        self.refresh_current_view()

    def on_tick(self):
        # Sincroniza flags desde la UI
        self.scheduler.simulate_zombie = self.chk_zombie.isChecked()
        self.scheduler.repeat_mode = self.chk_repeat.isChecked()
        auto_arrivals = self.chk_auto_arrivals.isChecked()
        auto_blocks = self.chk_auto_blocks.isChecked()

        # Avanza 1 tick
        self.scheduler.tick(auto_arrivals=auto_arrivals, auto_blocks=auto_blocks)
        self.update_pid_spin_range()
        self.refresh_current_view()

    def on_toggle_view(self, checked: bool):
        # Cambia entre vista unificada y dividida
        self.btn_toggle_view.setIcon(self.style().standardIcon(QStyle.SP_FileDialogDetailedView if checked else QStyle.SP_FileDialogListView))
        if checked:
            self.unified_container.hide()
            self.grouped_container.show()
            self.refresh_tables_grouped()
        else:
            self.grouped_container.hide()
            self.unified_container.show()
            self.refresh_table_all()

    # ----- Refresco de tablas -----
    def refresh_current_view(self):
        self.update_labels()
        if self.btn_toggle_view.isChecked():
            self.refresh_tables_grouped()
        else:
            self.refresh_table_all()

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
                prio = PRIO_LABEL[p.priority]
                cells = [str(p.pid), p.state.name, str(p.remaining_time), reason, waitfor, prio]
                for c, val in enumerate(cells):
                    tbl.setItem(r, c, QTableWidgetItem(val))
                color = STATE_COLORS.get(p.state)
                for c in range(len(cells)):
                    tbl.item(r, c).setBackground(color)

        fill(self.tbl_ready, [*pro_running, *pro_ready])
        fill(self.tbl_blocked, [*pro_blocked, *pro_paused])
        fill(self.tbl_done, [*pro_finished, *pro_zombie])

    def refresh_table_all(self):
        procs: List[Process] = []
        if self.scheduler.running: procs.append(self.scheduler.running)
        procs += list(self.scheduler.ready)
        procs += list(self.scheduler.blocked)
        procs += list(self.scheduler.zombies)
        procs += list(self.scheduler.finished)
        procs += list(self.scheduler.new)

        headers_count = 6
        self.tbl_all.setRowCount(len(procs))
        for r, p in enumerate(procs):
            reason = p.block_reason.name if p.block_reason else ""
            if p.block_reason == BlockReason.IO and p.io_remaining > 0:
                reason += f" ({p.io_remaining})"
            waitfor = str(p.waiting_for_pid) if p.waiting_for_pid is not None else ""
            prio = PRIO_LABEL[p.priority]
            cells = [str(p.pid), p.state.name, str(p.remaining_time), reason, waitfor, prio]
            for c, val in enumerate(cells):
                self.tbl_all.setItem(r, c, QTableWidgetItem(val))
            color = STATE_COLORS.get(p.state)
            for c in range(headers_count):
                self.tbl_all.item(r, c).setBackground(color)

# ----- Ejecutable -----
def main():
    import sys
    app = QApplication(sys.argv)
    w = MainWindow()
    w.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
