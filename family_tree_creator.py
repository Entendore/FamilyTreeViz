#!/usr/bin/env python3
"""
Family Tree Creator — Enhanced Visualization & Charts Edition
A PySide6 application for creating and visualizing family trees.
"""

import sys
import os
import json
import uuid
import random
import math
import time
import copy
from collections import deque

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QGraphicsScene, QGraphicsView,
    QGraphicsItem, QGraphicsPathItem, QGraphicsLineItem, QDialog, QVBoxLayout,
    QHBoxLayout, QFormLayout, QLabel, QLineEdit, QComboBox,
    QTextEdit, QPushButton, QToolBar, QFileDialog, QMessageBox,
    QDockWidget, QTreeWidget, QTreeWidgetItem, QMenu, QWidget,
    QGroupBox, QSizePolicy, QTabWidget, QShortcut,
)
from PySide6.QtCore import Qt, QPointF, QRectF, Signal, QTimer
from PySide6.QtGui import (
    QPainter, QPen, QBrush, QColor, QFont, QLinearGradient,
    QPainterPath, QAction, QPixmap, QPalette, QTransform, QKeySequence, QLineF,
)
from PySide6.QtWidgets import QUndoStack, QUndoCommand

# Matplotlib for Chart Making
import matplotlib
matplotlib.use('QtAgg')
from matplotlib.backends.backend_qtagg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.figure import Figure

# ─── Constants ────────────────────────────────────────────────────────────────
NODE_W = 210
NODE_H = 82
H_GAP = 50
V_GAP = 120
SPOUSE_GAP = 40
AVATAR_R = 16
CORNER_R = 10
SAMPLE_FILE = "sample_family_tree.json"

# ─── Color Palette ────────────────────────────────────────────────────────────
C = {
    "male":       QColor("#3B82F6"),
    "male_bg":    QColor("#DBEAFE"),
    "female":     QColor("#EC4899"),
    "female_bg":  QColor("#FCE7F3"),
    "other":      QColor("#8B5CF6"),
    "other_bg":   QColor("#EDE9FE"),
    "card":       QColor("#FFFFFF"),
    "shadow":     QColor(0, 0, 0, 22),
    "border":     QColor("#E5E7EB"),
    "border_hov": QColor("#CBD5E1"),
    "selected":   QColor("#3B82F6"),
    "text":       QColor("#1F2937"),
    "text2":      QColor("#6B7280"),
    "text3":      QColor("#9CA3AF"),
    "conn":       QColor("#94A3B8"),
    "conn_hi":    QColor("#3B82F6"),
    "spouse":     QColor("#F472B6"),
    "spouse_hi":  QColor("#EC4899"),
    "bg":         QColor("#F8FAFC"),
    "grid":       QColor("#E2E8F0"),
    "gen_lbl":    QColor("#CBD5E1"),
}

# Matplotlib color equivalents
MC = {
    "male": "#3B82F6",
    "female": "#EC4899",
    "other": "#8B5CF6",
    "alive": "#10B981",
    "deceased": "#6B7280",
    "bg": "#F8FAFC",
    "text": "#1F2937",
    "grid": "#E2E8F0",
}


# ─── Data Model ───────────────────────────────────────────────────────────────
class Person:
    def __init__(self, name="", gender="Male", birth_date="",
                 death_date="", notes="", person_id=None):
        self.id = person_id or str(uuid.uuid4())
        self.name = name
        self.gender = gender
        self.birth_date = birth_date
        self.death_date = death_date
        self.notes = notes

    def to_dict(self):
        return dict(id=self.id, name=self.name, gender=self.gender,
                    birth_date=self.birth_date, death_date=self.death_date,
                    notes=self.notes)

    @classmethod
    def from_dict(cls, d):
        return cls(name=d.get("name", ""), gender=d.get("gender", "Male"),
                   birth_date=d.get("birth_date", ""),
                   death_date=d.get("death_date", ""),
                   notes=d.get("notes", ""), person_id=d.get("id"))


class FamilyTreeModel:
    def __init__(self):
        self.persons: dict[str, Person] = {}
        self.parent_child: list[tuple[str, str]] = []
        self.spouses: list[tuple[str, str]] = []

    def add_person(self, p: Person): self.persons[p.id] = p

    def remove_person(self, pid: str):
        self.persons.pop(pid, None)
        self.parent_child = [(p, c) for p, c in self.parent_child if p != pid and c != pid]
        self.spouses = [s for s in self.spouses if pid not in s]

    def add_parent_child(self, parent_id: str, child_id: str) -> bool:
        if parent_id == child_id or (parent_id, child_id) in self.parent_child: return False
        if self._is_ancestor(child_id, parent_id): return False
        self.parent_child.append((parent_id, child_id))
        return True

    def add_spouse(self, id1: str, id2: str):
        pair = tuple(sorted([id1, id2]))
        if id1 != id2 and pair not in self.spouses: self.spouses.append(pair)

    def _is_ancestor(self, potential_ancestor, person_id):
        queue = deque([person_id]); visited = set()
        while queue:
            current = queue.popleft()
            if current == potential_ancestor: return True
            if current in visited: continue
            visited.add(current)
            for p in self.get_parents(current): queue.append(p)
        return False

    def get_parents(self, pid: str) -> list[str]: return [p for p, c in self.parent_child if c == pid]
    def get_children(self, pid: str) -> list[str]: return [c for p, c in self.parent_child if p == pid]
    def get_spouses(self, pid: str) -> list[str]: return [p2 if p1 == pid else p1 for p1, p2 in self.spouses if pid in (p1, p2)]
    def get_roots(self) -> list[str]: return [pid for pid in self.persons if pid not in {c for _, c in self.parent_child}]
    def get_family_children(self, pids: list[str]) -> list[str]:
        ch = set()
        for pid in pids: ch.update(self.get_children(pid))
        return list(ch)

    def get_family_units(self) -> list[tuple[frozenset, list]]:
        child_to_parents: dict[str, set[str]] = {}
        for parent_id, child_id in self.parent_child:
            if child_id not in child_to_parents: child_to_parents[child_id] = set()
            child_to_parents[child_id].add(parent_id)
        units: dict[frozenset, list] = {}
        for child_id, parent_set in child_to_parents.items():
            key = frozenset(parent_set)
            if key not in units: units[key] = []
            units[key].append(child_id)
        return list(units.items())

    def to_dict(self):
        return dict(persons={pid: p.to_dict() for pid, p in self.persons.items()},
                    parent_child=self.parent_child, spouses=self.spouses)

    def from_dict(self, data: dict):
        self.persons.clear(); self.parent_child.clear(); self.spouses.clear()
        if not isinstance(data, dict):
            return
        persons_data = data.get("persons", {})
        if not isinstance(persons_data, dict):
            return
        for pd in persons_data.values():
            if not isinstance(pd, dict):
                continue
            try:
                p = Person.from_dict(pd); self.persons[p.id] = p
            except Exception:
                continue
        raw_pc = data.get("parent_child", [])
        if isinstance(raw_pc, list):
            for x in raw_pc:
                if isinstance(x, (list, tuple)) and len(x) >= 2 and x[0] in self.persons and x[1] in self.persons:
                    self.parent_child.append((str(x[0]), str(x[1])))
        raw_sp = data.get("spouses", [])
        if isinstance(raw_sp, list):
            for x in raw_sp:
                if isinstance(x, (list, tuple)) and len(x) >= 2 and x[0] in self.persons and x[1] in self.persons:
                    self.spouses.append((str(x[0]), str(x[1])))


# ─── Utility: Parse Year ─────────────────────────────────────────────────────
import re as _re

def _parse_year(date_str: str) -> int | None:
    """Extract a 4-digit year from a date string like '1965', '1965-03-15', 'Mar 1965'."""
    if not date_str:
        return None
    m = _re.search(r'\b(18|19|20)\d{2}\b', date_str)
    return int(m.group()) if m else None


def _compute_age(birth: str, death: str) -> str:
    """Return a human-readable age string from birth/death date strings."""
    by = _parse_year(birth)
    if by is None:
        return "Unknown"
    dy = _parse_year(death)
    if dy is None:
        return f"{2026 - by} (living)"
    age = dy - by
    if age < 0:
        return "Invalid"
    return str(age)


def _find_path(model: FamilyTreeModel, start_id: str, end_id: str) -> list[str] | None:
    """BFS to find shortest relationship path between two people. Returns list of person IDs or None."""
    if start_id == end_id:
        return [start_id]
    queue = deque([(start_id, [start_id])])
    visited = {start_id}
    while queue:
        cur, path = queue.popleft()
        # Expand to parents, children, and spouses
        neighbors = []
        neighbors.extend(model.get_parents(cur))
        neighbors.extend(model.get_children(cur))
        neighbors.extend(model.get_spouses(cur))
        for nxt in neighbors:
            if nxt == end_id:
                return path + [nxt]
            if nxt not in visited:
                visited.add(nxt)
                queue.append((nxt, path + [nxt]))
    return None


# ─── Undo / Redo Commands ────────────────────────────────────────────────────
class AddPersonCommand(QUndoCommand):
    def __init__(self, model: FamilyTreeModel, person: Person):
        super().__init__(f"Add '{person.name}'")
        self.model = model
        self.person = person
        self._done = False

    def undo(self):
        self.model.remove_person(self.person.id)
        self._done = False

    def redo(self):
        self.model.add_person(self.person)
        self._done = True


class RemovePersonCommand(QUndoCommand):
    def __init__(self, model: FamilyTreeModel, pid: str):
        p = model.persons[pid]
        super().__init__(f"Remove '{p.name}'")
        self.model = model
        self.snapshot = model.to_dict()
        self.pid = pid

    def undo(self):
        self.model.from_dict(self.snapshot)

    def redo(self):
        self.model.remove_person(self.pid)


class EditPersonCommand(QUndoCommand):
    def __init__(self, model: FamilyTreeModel, pid: str, old_person: Person, new_person: Person):
        super().__init__(f"Edit '{old_person.name}'")
        self.model = model
        self.pid = pid
        self.old_data = old_person.to_dict()
        self.new_data = new_person.to_dict()

    def undo(self):
        p = self.model.persons.get(self.pid)
        if p:
            for k, v in self.old_data.items():
                if k != 'id':
                    setattr(p, k, v)

    def redo(self):
        p = self.model.persons.get(self.pid)
        if p:
            for k, v in self.new_data.items():
                if k != 'id':
                    setattr(p, k, v)


class AddRelationCommand(QUndoCommand):
    def __init__(self, model: FamilyTreeModel, rel_type: str, id1: str, id2: str):
        label = "parent-child" if rel_type == "pc" else "spouse"
        n1 = model.persons[id1].name if id1 in model.persons else "?"
        n2 = model.persons[id2].name if id2 in model.persons else "?"
        super().__init__(f"Add {label}: {n1} -> {n2}")
        self.model = model
        self.rel_type = rel_type
        self.id1 = id1
        self.id2 = id2

    def undo(self):
        if self.rel_type == "pc":
            self.model.parent_child = [(p, c) for p, c in self.model.parent_child if not (p == self.id1 and c == self.id2)]
        else:
            pair = tuple(sorted([self.id1, self.id2]))
            if pair in self.model.spouses:
                self.model.spouses.remove(pair)

    def redo(self):
        if self.rel_type == "pc":
            if (self.id1, self.id2) not in self.model.parent_child:
                self.model.parent_child.append((self.id1, self.id2))
        else:
            self.model.add_spouse(self.id1, self.id2)


class DuplicatePersonCommand(QUndoCommand):
    """Clone a person — undo removes the new person entirely."""
    def __init__(self, model: FamilyTreeModel, source_id: str, new_person: Person):
        src = model.persons[source_id]
        super().__init__(f"Duplicate '{src.name}'")
        self.model = model
        self.new_person = new_person
        self._done = False

    def undo(self):
        self.model.remove_person(self.new_person.id)
        self._done = False

    def redo(self):
        self.model.add_person(self.new_person)
        self._done = True


class DisconnectAllCommand(QUndoCommand):
    """Remove all relationships involving a person without deleting the person."""
    def __init__(self, model: FamilyTreeModel, pid: str):
        p = model.persons[pid]
        super().__init__(f"Disconnect '{p.name}'")
        self.model = model
        self.pid = pid
        self.snapshot = model.to_dict()

    def undo(self):
        self.model.from_dict(self.snapshot)

    def redo(self):
        self.model.parent_child = [
            (p, c) for p, c in self.model.parent_child
            if p != self.pid and c != self.pid
        ]
        self.model.spouses = [
            s for s in self.model.spouses if self.pid not in s
        ]


class RemoveRelationCommand(QUndoCommand):
    def __init__(self, model: FamilyTreeModel, rel_type: str, id1: str, id2: str):
        label = "parent-child" if rel_type == "pc" else "spouse"
        n1 = model.persons[id1].name if id1 in model.persons else "?"
        n2 = model.persons[id2].name if id2 in model.persons else "?"
        super().__init__(f"Remove {label}: {n1} -> {n2}")
        self.model = model
        self.rel_type = rel_type
        self.id1 = id1
        self.id2 = id2

    def undo(self):
        if self.rel_type == "pc":
            if (self.id1, self.id2) not in self.model.parent_child:
                self.model.parent_child.append((self.id1, self.id2))
        else:
            self.model.add_spouse(self.id1, self.id2)

    def redo(self):
        if self.rel_type == "pc":
            self.model.parent_child = [(p, c) for p, c in self.model.parent_child if not (p == self.id1 and c == self.id2)]
        else:
            pair = tuple(sorted([self.id1, self.id2]))
            if pair in self.model.spouses:
                self.model.spouses.remove(pair)


# ─── Graphics Items ───────────────────────────────────────────────────────────
class PersonNode(QGraphicsItem):
    def __init__(self, person: Person):
        super().__init__()
        self.person = person
        self.setFlag(QGraphicsItem.ItemIsMovable)
        self.setFlag(QGraphicsItem.ItemIsSelectable)
        self.setFlag(QGraphicsItem.ItemSendsGeometryChanges)
        self.setCursor(Qt.PointingHandCursor)
        self.setAcceptHoverEvents(True)
        self._hover = False
        self._highlight = False

    @property
    def accent(self):
        if self.person.gender == "Male": return C["male"]
        if self.person.gender == "Female": return C["female"]
        return C["other"]

    def boundingRect(self): return QRectF(-4, -4, NODE_W + 8, NODE_H + 8)

    def shape(self):
        path = QPainterPath(); path.addRoundedRect(QRectF(0, 0, NODE_W, NODE_H), CORNER_R, CORNER_R); return path

    def paint(self, painter: QPainter, option, widget):
        painter.setRenderHint(QPainter.Antialiasing)
        r = QRectF(0, 0, NODE_W, NODE_H)
        is_deceased = bool(self.person.death_date)

        painter.setPen(Qt.NoPen); painter.setBrush(C["shadow"])
        painter.drawRoundedRect(r.translated(2, 3), CORNER_R, CORNER_R)

        if self.isSelected(): border, bw = C["selected"], 2.0
        elif self._hover or self._highlight: border, bw = C["border_hov"], 1.4
        else: border, bw = C["border"], 1.0
        
        painter.setPen(QPen(border, bw)); painter.setBrush(C["card"])
        painter.drawRoundedRect(r, CORNER_R, CORNER_R)

        clip = QPainterPath(); clip.addRoundedRect(r, CORNER_R, CORNER_R); painter.setClipPath(clip)
        painter.setPen(Qt.NoPen); painter.setBrush(self.accent)
        painter.drawRect(QRectF(0, 0, 5, NODE_H)); painter.setClipping(False)

        ax, ay = 26, NODE_H / 2
        painter.setPen(Qt.NoPen); painter.setBrush(self.accent)
        painter.drawEllipse(QPointF(ax, ay), AVATAR_R, AVATAR_R)

        painter.setFont(QFont("Segoe UI", 10, QFont.Bold)); painter.setPen(QColor("#FFFFFF"))
        initial = self.person.name[0].upper() if self.person.name else "?"
        painter.drawText(QRectF(ax - AVATAR_R, ay - AVATAR_R, AVATAR_R * 2, AVATAR_R * 2), Qt.AlignCenter, initial)

        nx, nw = ax + AVATAR_R + 10, NODE_W - (ax + AVATAR_R + 10) - 12
        painter.setFont(QFont("Segoe UI", 10, QFont.Bold)); painter.setPen(C["text"] if not is_deceased else C["text2"])
        name = self.person.name
        while painter.fontMetrics().horizontalAdvance(name) > nw and name: name = name[:-1]
        if name != self.person.name: name += "…"
        painter.drawText(QRectF(nx, 14, nw, 22), Qt.AlignVCenter | Qt.AlignLeft, name)

        painter.setFont(QFont("Segoe UI", 8)); painter.setPen(C["text2"])
        dt = ""
        if self.person.birth_date: dt = f"b. {self.person.birth_date}"
        if self.person.death_date: dt += ("  ✝ " if dt else "✝ ") + self.person.death_date
        painter.drawText(QRectF(nx, 36, nw, 20), Qt.AlignVCenter | Qt.AlignLeft, dt)

        if is_deceased:
            painter.setFont(QFont("Segoe UI", 7)); painter.setPen(C["text3"])
            painter.drawText(QRectF(NODE_W - 32, 5, 28, 14), Qt.AlignCenter, "✝ Rest")

    def setHighlight(self, on: bool): self._highlight = on; self.update()
    def hoverEnterEvent(self, ev): self._hover = True; self.update(); super().hoverEnterEvent(ev)
    def hoverLeaveEvent(self, ev): self._hover = False; self.update(); super().hoverLeaveEvent(ev)
    def mouseDoubleClickEvent(self, ev):
        if self.scene() and hasattr(self.scene(), "edit_person_requested"): self.scene().edit_person_requested.emit(self.person.id)
        super().mouseDoubleClickEvent(ev)

    def keyPressEvent(self, ev):
        if ev.key() == Qt.Key_F2 and self.scene() and hasattr(self.scene(), "rename_person_requested"):
            self.scene().rename_person_requested.emit(self.person.id)
            ev.accept()
            return
        super().keyPressEvent(ev)

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemPositionHasChanged:
            sc = self.scene()
            if sc and hasattr(sc, 'update_connectors') and not getattr(sc, '_animating', False): sc.update_connectors()
        return super().itemChange(change, value)

    def bottom_center(self): return self.pos() + QPointF(NODE_W / 2, NODE_H)
    def top_center(self): return self.pos() + QPointF(NODE_W / 2, 0)


class FamilyBracket(QGraphicsPathItem):
    def __init__(self, parent_nodes: list[PersonNode], child_nodes: list[PersonNode]):
        super().__init__()
        self.parent_nodes = parent_nodes; self.child_nodes = child_nodes
        self.setZValue(-1); self._highlighted = False; self.update_path()

    def setHighlighted(self, on: bool): self._highlighted = on; self.update()
    
    def update_path(self):
        path = QPainterPath()
        if not self.child_nodes or not self.parent_nodes:
            self.setPath(path); return
        if not all(n.scene() is not None for n in self.parent_nodes + self.child_nodes):
            self.setPath(path); return
        if len(self.parent_nodes) >= 2:
            bottoms = [n.pos() + QPointF(NODE_W / 2, NODE_H) for n in self.parent_nodes]
            px, py = sum(b.x() for b in bottoms) / len(bottoms), max(b.y() for b in bottoms)
        else: pt = self.parent_nodes[0].bottom_center(); px, py = pt.x(), pt.y()

        child_tops = sorted([n.top_center() for n in self.child_nodes], key=lambda p: p.x())
        if not child_tops: self.setPath(path); return
        min_cy = min(ct.y() for ct in child_tops); jy = (py + min_cy) / 2

        path.moveTo(px, py); path.lineTo(px, jy)
        if len(child_tops) == 1:
            cx = child_tops[0].x()
            if abs(px - cx) >= 0.5: path.lineTo(cx, jy); path.lineTo(cx, child_tops[0].y())
            else: path.lineTo(cx, child_tops[0].y())
        else:
            lx, rx = child_tops[0].x(), child_tops[-1].x()
            bl, br = min(lx, px), max(rx, px)
            path.moveTo(bl, jy); path.lineTo(br, jy)
            for ct in child_tops: path.moveTo(ct.x(), jy); path.lineTo(ct.x(), ct.y())
        self.setPath(path)

    def paint(self, painter, option, widget):
        painter.setRenderHint(QPainter.Antialiasing)
        pen = QPen(C["conn_hi"] if self._highlighted else C["conn"], 1.8, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin)
        painter.setPen(pen); painter.setBrush(Qt.NoBrush); painter.drawPath(self.path())
        
        if self.parent_nodes:
            if len(self.parent_nodes) >= 2:
                bottoms = [n.pos() + QPointF(NODE_W / 2, NODE_H) for n in self.parent_nodes]
                px, py = sum(b.x() for b in bottoms) / len(bottoms), max(b.y() for b in bottoms)
            else: pt = self.parent_nodes[0].bottom_center(); px, py = pt.x(), pt.y()
            if self.child_nodes:
                min_cy = min(n.top_center().y() for n in self.child_nodes); jy = (py + min_cy) / 2
                painter.setPen(Qt.NoPen); painter.setBrush(C["conn_hi"] if self._highlighted else C["conn"])
                painter.drawEllipse(QPointF(px, jy), 3, 3)

        painter.setPen(Qt.NoPen); painter.setBrush(C["conn_hi"] if self._highlighted else C["conn"])
        for cn in self.child_nodes:
            ct = cn.top_center(); sz = 5
            painter.drawPolygon([QPointF(ct.x(), ct.y()), QPointF(ct.x() - sz, ct.y() - sz * 1.6), QPointF(ct.x() + sz, ct.y() - sz * 1.6)])


class SpouseLink(QGraphicsPathItem):
    def __init__(self, node1: PersonNode, node2: PersonNode):
        super().__init__()
        self.node1 = node1; self.node2 = node2; self.setZValue(-0.5); self._highlighted = False; self.update_path()

    def setHighlighted(self, on: bool): self._highlighted = on; self.update()

    def _anchors(self):
        if self.node1.scene() is None or self.node2.scene() is None:
            return (QPointF(0, 0), QPointF(0, 0))
        if self.node1.pos().x() < self.node2.pos().x(): return (self.node1.pos() + QPointF(NODE_W, NODE_H / 2), self.node2.pos() + QPointF(0, NODE_H / 2))
        return (self.node2.pos() + QPointF(NODE_W, NODE_H / 2), self.node1.pos() + QPointF(0, NODE_H / 2))

    def update_path(self):
        path = QPainterPath(); s, e = self._anchors(); mx = (s.x() + e.x()) / 2
        path.moveTo(s); path.cubicTo(QPointF(mx, s.y()), QPointF(mx, e.y()), e); self.setPath(path)

    def paint(self, painter, option, widget):
        painter.setRenderHint(QPainter.Antialiasing)
        color = C["spouse_hi"] if self._highlighted else C["spouse"]
        painter.setPen(QPen(color, 1.8, Qt.DashLine, Qt.RoundCap)); painter.setBrush(Qt.NoBrush); painter.drawPath(self.path())
        s, e = self._anchors(); mid = (s + e) / 2
        painter.setPen(Qt.NoPen); painter.setBrush(color); painter.drawEllipse(mid, 5, 5)
        painter.setBrush(C["card"]); painter.drawEllipse(mid, 3, 3); painter.setBrush(color); painter.drawEllipse(mid, 1.5, 1.5)


# ─── MCTS Layout Optimizer ─────────────────────────────────────────────────
class MCTSNode:
    """A node in the Monte Carlo search tree for layout optimization."""
    __slots__ = ('state', 'parent', 'children', 'visits', 'total_score', 'untried')

    def __init__(self, state: dict, parent=None):
        self.state = state        # child_order dict: parent_pid -> list of child pids
        self.parent = parent
        self.children: list['MCTSNode'] = []
        self.visits = 0
        self.total_score = 0.0
        self.untried = list(state.keys())  # parent pids whose child order hasn't been shuffled yet

    def ucb1(self, c: float = 1.414) -> float:
        if self.visits == 0:
            return float('inf')
        return (self.total_score / self.visits) + c * math.sqrt(math.log(self.parent.visits) / self.visits)

    def best_child(self, c: float = 1.414) -> 'MCTSNode':
        return max(self.children, key=lambda ch: ch.ucb1(c))

    def best_action_child(self) -> 'MCTSNode':
        """Return child with highest average score (for final decision)."""
        return max(self.children, key=lambda ch: ch.total_score / max(ch.visits, 1))


class MCTSOptimizer:
    """
    Uses Monte Carlo Tree Search to find a better child ordering
    for the family tree layout. The search space is the set of all
    permutations of children within each family unit.
    """

    def __init__(self, model: FamilyTreeModel, iterations: int = 2000, time_limit: float = 3.0):
        self.model = model
        self.iterations = iterations
        self.time_limit = time_limit

    def _get_family_groups(self) -> dict[str, list[str]]:
        """Returns parent_key -> list of children for each family unit."""
        groups: dict[str, list[str]] = {}
        for parent_ids, child_ids in self.model.get_family_units():
            key = "|".join(sorted(parent_ids))
            groups[key] = list(child_ids)
        return groups

    def _evaluate_layout(self, child_orders: dict[str, list[str]]) -> float:
        """
        Score a layout configuration (child ordering). Higher is better.
        Considers: edge crossing reduction, left-to-right ordering consistency,
        and spouse proximity.
        """
        score = 0.0
        names = {pid: p.name for pid, p in self.model.persons.items()}

        for key, children in child_orders.items():
            parent_ids = key.split("|")
            if len(children) < 2:
                continue

            # Reward alphabetical name ordering (natural reading order)
            child_names = [names.get(c, "") for c in children]
            sorted_names = sorted(child_names, key=str.lower)
            name_order_score = sum(1 for a, b in zip(child_names, sorted_names) if a == b)
            score += name_order_score / max(len(children), 1)

            # Reward birth date ordering (chronological)
            birth_years = []
            for c in children:
                by = _parse_year(self.model.persons[c].birth_date) if c in self.model.persons else None
                birth_years.append(by)
            if all(by is not None for by in birth_years):
                chronological = sorted(birth_years)
                date_score = sum(1 for a, b in zip(birth_years, chronological) if a == b)
                score += date_score / max(len(children), 1) * 0.8  # slightly less weight

            # Reward gender clustering (males together, females together)
            genders = [self.model.persons[c].gender if c in self.model.persons else "" for c in children]
            transitions = sum(1 for i in range(1, len(genders)) if genders[i] != genders[i - 1])
            score += max(0, 1.0 - transitions / max(len(children) - 1, 1)) * 0.5

            # Reward spouse-sibling consistency: if a child has a spouse,
            # try to place them near siblings of same generation
            for i, cid in enumerate(children):
                spouses = self.model.get_spouses(cid)
                for sid in spouses:
                    if sid in children:
                        j = children.index(sid)
                        score -= abs(i - j) * 0.1  # penalize distance between spouses

        # Reward cross-generation alignment: children at similar x positions as parents
        gens = {}
        roots = self.model.get_roots()
        q: deque[str] = deque()
        for r in roots:
            gens[r] = 0
            q.append(r)
        visited: set[str] = set()
        while q:
            cur = q.popleft()
            if cur in visited:
                continue
            visited.add(cur)
            g = gens[cur]
            for c in self.model.get_children(cur):
                ng = g + 1
                gens[c] = ng if c not in gens else max(gens[c], ng)
                if c not in visited:
                    q.append(c)

        # Normalize by number of family groups to keep scores comparable
        n_groups = max(len(child_orders), 1)
        return score / n_groups

    def _get_initial_orders(self, groups: dict[str, list[str]]) -> dict[str, list[str]]:
        return {key: list(children) for key, children in groups.items()}

    def optimize(self, progress_callback=None) -> dict[str, list[str]] | None:
        """
        Run MCTS optimization. Returns the best child ordering or None.
        progress_callback(iteration, total) is called periodically.
        """
        groups = self._get_family_groups()
        if not groups or all(len(ch) < 2 for ch in groups.values()):
            return None  # Nothing to optimize (no families with 2+ children)

        # Filter to only groups with 2+ children
        optimizable = {k: v for k, v in groups.items() if len(v) >= 2}
        if not optimizable:
            return None

        initial_orders = self._get_initial_orders(optimizable)
        root = MCTSNode(copy.deepcopy(initial_orders))

        start_time = time.time()
        for i in range(self.iterations):
            if time.time() - start_time > self.time_limit:
                break

            node = root
            # Selection: traverse tree using UCB1
            while not node.untried and node.children:
                node = node.best_child()

            # Expansion: add a new child by shuffling one family's child order
            if node.untried:
                key = random.choice(node.untried)
                node.untried.remove(key)

                new_state = copy.deepcopy(node.state)
                children = list(new_state[key])
                # Perform a random swap or shuffle
                if len(children) == 2:
                    children.reverse()
                else:
                    # Swap two random positions
                    a, b = random.sample(range(len(children)), 2)
                    children[a], children[b] = children[b], children[a]
                new_state[key] = children

                child = MCTSNode(new_state, parent=node)
                node.children.append(child)
                node = child

            # Simulation (rollout): evaluate this state
            score = self._evaluate_layout(node.state)

            # Add noise for exploration diversity
            score += random.gauss(0, 0.02)

            # Backpropagation
            while node is not None:
                node.visits += 1
                node.total_score += score
                node = node.parent

            if progress_callback and i % 100 == 0:
                progress_callback(i, self.iterations)

        if not root.children:
            return None

        best = root.best_action_child()
        return best.state if best.total_score / max(best.visits, 1) > self._evaluate_layout(initial_orders) else None

    @staticmethod
    def apply_orders(model: FamilyTreeModel, orders: dict[str, list[str]]):
        """
        Rebuild parent_child list to reflect the new child ordering.
        This doesn't change relationships, only the order they're stored/traversed.
        """
        # Build a mapping of (parent_key) -> ordered children
        order_map: dict[frozenset, list[str]] = {}
        for key, children in orders.items():
            parent_ids = frozenset(key.split("|"))
            order_map[parent_ids] = children

        # Rebuild parent_child maintaining order
        new_pc: list[tuple[str, str]] = []
        placed_children: set[str] = set()

        for parent_ids, ordered_children in order_map.items():
            for pid in parent_ids:
                for cid in ordered_children:
                    if (pid, cid) in model.parent_child:
                        new_pc.append((pid, cid))
                        placed_children.add(cid)

        # Add any remaining relationships not in optimizable groups
        for pc in model.parent_child:
            if pc not in new_pc:
                new_pc.append(pc)

        model.parent_child = new_pc


# ─── AI Insights Engine ───────────────────────────────────────────────────
class Insight:
    """A single AI-generated insight about the family tree."""
    __slots__ = ('severity', 'category', 'title', 'description', 'person_ids', 'fix_type', 'fix_data')

    def __init__(self, severity: str, category: str, title: str, description: str,
                 person_ids: list[str] = None, fix_type: str = "", fix_data: dict = None):
        self.severity = severity        # "error", "warning", "info", "suggestion"
        self.category = category        # "duplicate", "date", "relationship", "data", "structure"
        self.title = title
        self.description = description
        self.person_ids = person_ids or []
        self.fix_type = fix_type        # "add_spouse", "connect_parent", "merge", ""
        self.fix_data = fix_data or {}


class AIInsightsEngine:
    """
    Rule-based AI analysis engine that scans the family tree for issues,
    inconsistencies, and improvement suggestions.
    """

    def __init__(self, model: FamilyTreeModel):
        self.model = model
        self.names = {pid: p.name for pid, p in model.persons.items()}

    def _levenshtein(self, s1: str, s2: str) -> int:
        """Compute Levenshtein edit distance between two strings."""
        if len(s1) < len(s2):
            return self._levenshtein(s2, s1)
        if len(s2) == 0:
            return len(s1)
        prev = list(range(len(s2) + 1))
        for i, c1 in enumerate(s1):
            curr = [i + 1]
            for j, c2 in enumerate(s2):
                curr.append(min(prev[j + 1] + 1, curr[j] + 1, prev[j] + (c1 != c2)))
            prev = curr
        return prev[-1]

    def _extract_surname(self, name: str) -> str:
        """Extract surname (last word) from a full name."""
        parts = name.strip().split()
        return parts[-1].lower() if parts else ""

    def analyze(self) -> list[Insight]:
        """Run all analysis checks and return a list of insights."""
        insights: list[Insight] = []
        if not self.model.persons:
            return insights
        insights.extend(self._find_orphans())
        insights.extend(self._find_potential_duplicates())
        insights.extend(self._find_date_inconsistencies())
        insights.extend(self._find_missing_spouses())
        insights.extend(self._find_incomplete_data())
        insights.extend(self._find_age_anomalies())
        insights.extend(self._find_single_parents())
        insights.extend(self._find_disconnected_subtrees())
        return insights

    def _find_orphans(self) -> list[Insight]:
        """Find nodes with no relationships at all."""
        results = []
        for pid, p in self.model.persons.items():
            has_rel = (bool(self.model.get_parents(pid)) or
                       bool(self.model.get_children(pid)) or
                       bool(self.model.get_spouses(pid)))
            if not has_rel:
                results.append(Insight(
                    severity="warning",
                    category="structure",
                    title=f"'{p.name}' has no relationships",
                    description=f"{p.name} exists in the tree but is not connected to anyone. "
                                f"Consider connecting them to a family unit or removing them.",
                    person_ids=[pid],
                ))
        return results

    def _find_potential_duplicates(self) -> list[Insight]:
        """Find persons with very similar names (possible duplicates)."""
        results = []
        pids = list(self.model.persons.keys())
        for i in range(len(pids)):
            for j in range(i + 1, len(pids)):
                a, b = pids[i], pids[j]
                na, nb = self.model.persons[a].name, self.model.persons[b].name
                if na.lower() == nb.lower():
                    results.append(Insight(
                        severity="error",
                        category="duplicate",
                        title=f"Exact duplicate name: '{na}'",
                        description=f"'{na}' appears twice (IDs differ). These may be the same person. "
                                    f"Consider merging them.",
                        person_ids=[a, b],
                    ))
                elif self._levenshtein(na.lower(), nb.lower()) <= 2 and len(na) > 4:
                    results.append(Insight(
                        severity="warning",
                        category="duplicate",
                        title=f"Similar names: '{na}' and '{nb}'",
                        description=f"These names are very similar (edit distance "
                                    f"{self._levenshtein(na.lower(), nb.lower())}). They might be duplicates.",
                        person_ids=[a, b],
                    ))
        return results

    def _find_date_inconsistencies(self) -> list[Insight]:
        """Find impossible or unlikely date combinations."""
        results = []
        for pid, p in self.model.persons.items():
            by = _parse_year(p.birth_date)
            dy = _parse_year(p.death_date)
            if by is not None and dy is not None:
                if dy < by:
                    results.append(Insight(
                        severity="error",
                        category="date",
                        title=f"Death before birth: {p.name}",
                        description=f"{p.name} has birth year {by} but death year {dy}.",
                        person_ids=[pid],
                    ))
                elif dy - by > 120:
                    results.append(Insight(
                        severity="warning",
                        category="date",
                        title=f"Unlikely lifespan: {p.name} ({dy - by} years)",
                        description=f"{p.name} lived {dy - by} years, which is extremely unusual.",
                        person_ids=[pid],
                    ))

            # Check parent-child date consistency
            for parent_id in self.model.get_parents(pid):
                pp = self.model.persons.get(parent_id)
                if pp and by is not None:
                    pby = _parse_year(pp.birth_date)
                    if pby is not None:
                        age_at_child = by - pby
                        if age_at_child < 12:
                            results.append(Insight(
                                severity="error",
                                category="date",
                                title=f"Parent too young: {pp.name} → {p.name}",
                                description=f"{pp.name} was only {age_at_child} when {p.name} was born.",
                                person_ids=[parent_id, pid],
                            ))
                        elif age_at_child > 65:
                            results.append(Insight(
                                severity="info",
                                category="date",
                                title=f"Parent age at birth: {pp.name} was {age_at_child}",
                                description=f"{pp.name} was {age_at_child} when {p.name} was born. "
                                            f"This is uncommon but possible.",
                                person_ids=[parent_id, pid],
                            ))
        return results

    def _find_missing_spouses(self) -> list[Insight]:
        """Find parents who share children but aren't marked as spouses."""
        results = []
        for parent_ids, child_ids in self.model.get_family_units():
            if len(parent_ids) >= 2:
                parent_list = list(parent_ids)
                for i in range(len(parent_list)):
                    for j in range(i + 1, len(parent_list)):
                        a, b = parent_list[i], parent_list[j]
                        pair = tuple(sorted([a, b]))
                        if pair not in self.model.spouses:
                            na = self.names.get(a, "?")
                            nb = self.names.get(b, "?")
                            results.append(Insight(
                                severity="suggestion",
                                category="relationship",
                                title=f"Possible spouses: {na} & {nb}",
                                description=f"{na} and {nb} share {len(child_ids)} child(ren) but aren't "
                                            f"marked as spouses. Consider connecting them.",
                                person_ids=[a, b],
                                fix_type="add_spouse",
                                fix_data={"id1": a, "id2": b},
                            ))
        return results

    def _find_incomplete_data(self) -> list[Insight]:
        """Find persons missing common data fields."""
        results = []
        total = len(self.model.persons)
        no_birth = sum(1 for p in self.model.persons.values() if not p.birth_date)
        no_gender = sum(1 for p in self.model.persons.values() if p.gender == "Other" and not p.name)

        if no_birth > 0 and total > 1:
            pct = no_birth * 100 // total
            results.append(Insight(
                severity="info",
                category="data",
                title=f"{no_birth} person(s) missing birth date ({pct}%)",
                description=f"Adding birth dates improves generation calculations, age statistics, "
                            f"and chronological layout accuracy.",
                person_ids=[pid for pid, p in self.model.persons.items() if not p.birth_date],
            ))

        no_notes = sum(1 for p in self.model.persons.values() if not p.notes)
        if no_notes == total and total > 3:
            results.append(Insight(
                severity="info",
                category="data",
                title="No notes on any person",
                description="Adding notes helps preserve family stories and context for future generations.",
                person_ids=[],
            ))
        return results

    def _find_age_anomalies(self) -> list[Insight]:
        """Find unusual age gaps between spouses."""
        results = []
        for a, b in self.model.spouses:
            pa, pb = self.model.persons.get(a), self.model.persons.get(b)
            if pa and pb:
                ya = _parse_year(pa.birth_date)
                yb = _parse_year(pb.birth_date)
                if ya is not None and yb is not None:
                    gap = abs(ya - yb)
                    if gap > 25:
                        results.append(Insight(
                            severity="info",
                            category="date",
                            title=f"Large age gap: {pa.name} & {pb.name} ({gap} years)",
                            description=f"There is a {gap}-year age difference between spouses. "
                                        f"Verify this is correct.",
                            person_ids=[a, b],
                        ))
        return results

    def _find_single_parents(self) -> list[Insight]:
        """Find children who have only one parent recorded."""
        results = []
        for parent_ids, child_ids in self.model.get_family_units():
            if len(parent_ids) == 1:
                pid = list(parent_ids)[0]
                pname = self.names.get(pid, "?")
                for cid in child_ids:
                    cname = self.names.get(cid, "?")
                    results.append(Insight(
                        severity="suggestion",
                        category="relationship",
                        title=f"Single parent: {cname} (only {pname} recorded)",
                        description=f"{cname} only has one parent on record. The other parent may be unknown "
                                    f"or not yet added to the tree.",
                        person_ids=[pid, cid],
                    ))
        return results

    def _find_disconnected_subtrees(self) -> list[Insight]:
        """Find groups of connected nodes not reachable from the main tree."""
        results = []
        if len(self.model.persons) < 2:
            return results

        # BFS from first person
        start = next(iter(self.model.persons))
        visited: set[str] = set()
        queue = deque([start])
        while queue:
            cur = queue.popleft()
            if cur in visited:
                continue
            visited.add(cur)
            for p in self.model.get_parents(cur):
                queue.append(p)
            for c in self.model.get_children(cur):
                queue.append(c)
            for s in self.model.get_spouses(cur):
                queue.append(s)

        unreachable = set(self.model.persons.keys()) - visited
        if unreachable:
            names = [self.names.get(pid, "?") for pid in unreachable]
            results.append(Insight(
                severity="warning",
                category="structure",
                title=f"{len(unreachable)} person(s) disconnected from main tree",
                description=f"The following people are not connected to the main family tree: "
                            f"{', '.join(names[:5])}{'...' if len(names) > 5 else ''}. "
                            f"Use Shift+Drag to connect them.",
                person_ids=list(unreachable),
            ))
        return results


# ─── AI Insights Dialog ───────────────────────────────────────────────────
class AIInsightsDialog(QDialog):
    """Dialog displaying AI-generated insights about the family tree."""

    SEVERITY_COLORS = {
        "error":     ("#DC2626", "#FEF2F2", "#991B1B"),
        "warning":   ("#D97706", "#FFFBEB", "#92400E"),
        "info":      ("#3B82F6", "#EFF6FF", "#1E40AF"),
        "suggestion":("#10B981", "#ECFDF5", "#065F46"),
    }
    CATEGORY_ICONS = {
        "duplicate":    "@@",
        "date":         "##",
        "relationship": ">>",
        "data":         "~~",
        "structure":    "||",
    }

    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent)
        self.model = model
        self.setWindowTitle("AI Tree Analysis")
        self.setMinimumSize(680, 520)
        self.setMaximumHeight(700)
        lay = QVBoxLayout(self)

        # Header with score
        header = QHBoxLayout()
        title = QLabel("AI Tree Analysis")
        title.setFont(QFont("Segoe UI", 14, QFont.Bold))
        header.addWidget(title)
        self.score_label = QLabel("")
        self.score_label.setFont(QFont("Segoe UI", 12, QFont.Bold))
        header.addStretch()
        header.addWidget(self.score_label)
        lay.addLayout(header)

        # Severity summary bar
        self.summary_bar = QLabel("")
        self.summary_bar.setStyleSheet(
            "padding: 8px; background: #F8FAFC; border-radius: 6px; "
            "border: 1px solid #E2E8F0; margin-bottom: 8px;")
        self.summary_bar.setWordWrap(True)
        lay.addWidget(self.summary_bar)

        # Tabs for categories
        self.tabs = QTabWidget()
        self.tabs.setStyleSheet("")
        lay.addWidget(self.tabs)

        # Buttons
        btns = QHBoxLayout()
        rerun = QPushButton("Re-analyze")
        rerun.setObjectName("accentBtn")
        rerun.clicked.connect(self._run_analysis)
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.close)
        btns.addStretch()
        btns.addWidget(rerun)
        btns.addWidget(close_btn)
        lay.addLayout(btns)

        self._fix_actions: list[tuple[Insight, QPushButton]] = []

        self._run_analysis()

    def _run_analysis(self):
        engine = AIInsightsEngine(self.model)
        self._insights = engine.analyze()
        self._build_ui()

    def _build_ui(self):
        # Clear old
        while self.tabs.count():
            self.tabs.removeTab(0)
        self._fix_actions.clear()

        insights = self._insights

        # Score calculation
        total = len(self.model.persons)
        errors = sum(1 for i in insights if i.severity == "error")
        warnings = sum(1 for i in insights if i.severity == "warning")
        suggestions = sum(1 for i in insights if i.severity == "suggestion")
        infos = sum(1 for i in insights if i.severity == "info")

        if errors == 0 and warnings == 0:
            score = 100
        else:
            score = max(0, 100 - errors * 15 - warnings * 5 - suggestions * 2)

        sc = "#10B981" if score >= 80 else "#D97706" if score >= 50 else "#DC2626"
        self.score_label.setText(f"Score: {score}/100")
        self.score_label.setStyleSheet(f"color: {sc};")

        self.summary_bar.setText(
            f"<b>{total}</b> members  |  "
            f"<span style='color:#DC2626'>{errors} errors</span>  |  "
            f"<span style='color:#D97706'>{warnings} warnings</span>  |  "
            f"<span style='color:#10B981'>{suggestions} suggestions</span>  |  "
            f"<span style='color:#3B82F6'>{infos} info</span>"
        )

        # Categorize
        by_cat: dict[str, list[Insight]] = {}
        for ins in insights:
            by_cat.setdefault(ins.category, []).append(ins)

        # "All" tab
        self.tabs.addTab(self._create_list(insights, "All"), f"All ({len(insights)})")

        # Individual category tabs
        cat_labels = {
            "duplicate": "Duplicates", "date": "Dates", "relationship": "Relationships",
            "data": "Data Quality", "structure": "Structure",
        }
        for cat, items in by_cat.items():
            label = cat_labels.get(cat, cat)
            self.tabs.addTab(self._create_list(items, cat), f"{label} ({len(items)})")

    def _create_list(self, insights: list[Insight], category: str) -> QWidget:
        w = QWidget()
        lay = QVBoxLayout(w)
        lay.setContentsMargins(4, 4, 4, 4)

        if not insights:
            empty = QLabel("No issues found in this category.")
            empty.setStyleSheet("color: #6B7280; padding: 20px;")
            empty.setAlignment(Qt.AlignCenter)
            lay.addWidget(empty)
            lay.addStretch()
            return w

        for ins in insights:
            row = QWidget()
            rl = QHBoxLayout(row)
            rl.setContentsMargins(0, 2, 0, 2)

            # Severity icon
            sev_colors = self.SEVERITY_COLORS.get(ins.severity, ("#6B7280", "#F3F4F6", "#374151"))
            icon_lbl = QLabel(self._severity_icon(ins.severity))
            icon_lbl.setFixedSize(28, 28)
            icon_lbl.setAlignment(Qt.AlignCenter)
            icon_lbl.setStyleSheet(
                f"background: {sev_colors[1]}; color: {sev_colors[0]}; "
                f"border-radius: 14px; font-weight: bold; font-size: 12px;")
            rl.addWidget(icon_lbl)

            # Text
            text_w = QWidget()
            tl = QVBoxLayout(text_w)
            tl.setContentsMargins(4, 0, 4, 0)
            title_lbl = QLabel(ins.title)
            title_lbl.setFont(QFont("Segoe UI", 9, QFont.Bold))
            title_lbl.setStyleSheet(f"color: {sev_colors[2]};")
            tl.addWidget(title_lbl)
            desc_lbl = QLabel(ins.description)
            desc_lbl.setWordWrap(True)
            desc_lbl.setStyleSheet(f"color: {sev_colors[2]}; font-size: 8pt; opacity: 0.8;")
            desc_lbl.setMaximumHeight(40)
            tl.addWidget(desc_lbl)
            rl.addWidget(text_w, 1)

            # Fix button for actionable items
            if ins.fix_type:
                fix_btn = QPushButton("Apply")
                fix_btn.setFixedSize(60, 26)
                fix_btn.setStyleSheet(
                    "background: #10B981; color: white; border: none; border-radius: 4px; font-size: 9pt;")
                fix_btn.clicked.connect(lambda checked, i=ins: self._apply_fix(i))
                rl.addWidget(fix_btn)

            lay.addWidget(row)

        lay.addStretch()
        return w

    def _severity_icon(self, sev: str) -> str:
        return {"error": "!!", "warning": "!?", "info": "ii", "suggestion": ">>"}.get(sev, "??")

    def _apply_fix(self, insight: Insight):
        if insight.fix_type == "add_spouse":
            id1, id2 = insight.fix_data["id1"], insight.fix_data["id2"]
            self.model.add_spouse(id1, id2)
            self._run_analysis()
        elif insight.fix_type == "connect_parent":
            pass  # Would need more complex dialog

    def get_insights(self) -> list[Insight]:
        return getattr(self, '_insights', [])


# ─── AI Smart Suggestions Panel ──────────────────────────────────────────
class AISuggestionsPanel(QWidget):
    """Live sidebar panel showing AI suggestions with quick actions."""
    fix_requested = Signal(str, str, dict)  # fix_type, fix_id, fix_data

    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent)
        self.model = model
        lay = QVBoxLayout(self)
        lay.setContentsMargins(4, 4, 4, 4)

        header = QLabel("AI Suggestions")
        header.setFont(QFont("Segoe UI", 10, QFont.Bold))
        lay.addWidget(header)

        self.score_bar = QLabel("")
        self.score_bar.setAlignment(Qt.AlignCenter)
        self.score_bar.setStyleSheet("padding: 6px; border-radius: 6px; margin-bottom: 4px;")
        lay.addWidget(self.score_bar)

        self.list_w = QTreeWidget()
        self.list_w.setHeaderLabels(["", "Suggestion"])
        self.list_w.setRootIsDecorated(False)
        self.list_w.setAlternatingRowColors(True)
        self.list_w.setColumnWidth(0, 28)
        lay.addWidget(self.list_w)

        btn_row = QHBoxLayout()
        self.analyze_btn = QPushButton("Analyze")
        self.analyze_btn.setObjectName("accentBtn")
        self.analyze_btn.clicked.connect(self.refresh)
        btn_row.addWidget(self.analyze_btn)
        lay.addLayout(btn_row)

        self._insights: list[Insight] = []

    def refresh(self):
        engine = AIInsightsEngine(self.model)
        self._insights = engine.analyze()
        self._populate()

    def _populate(self):
        self.list_w.clear()
        if not self._insights:
            item = QTreeWidgetItem(["", "No issues found"])
            self.list_w.addTopLevelItem(item)
            self.score_bar.setText("Score: 100/100")
            self.score_bar.setStyleSheet("background: #ECFDF5; color: #065F46; border: 1px solid #A7F3D0;")
            return

        errors = sum(1 for i in self._insights if i.severity == "error")
        warnings = sum(1 for i in self._insights if i.severity == "warning")
        suggestions = sum(1 for i in self._insights if i.severity == "suggestion")
        score = max(0, 100 - errors * 15 - warnings * 5 - suggestions * 2)

        sc = "#065F46" if score >= 80 else "#92400E" if score >= 50 else "#991B1B"
        bg = "#ECFDF5" if score >= 80 else "#FFFBEB" if score >= 50 else "#FEF2F2"
        self.score_bar.setText(f"Score: {score}/100  ({len(self._insights)} items)")
        self.score_bar.setStyleSheet(f"background: {bg}; color: {sc}; border: 1px solid #E2E8F0;")

        sev_icons = {"error": "!!", "warning": "!?", "suggestion": ">>", "info": "ii"}
        sev_colors = {"error": "#DC2626", "warning": "#D97706", "suggestion": "#10B981", "info": "#3B82F6"}

        # Show only errors, warnings, and suggestions (skip info in sidebar)
        shown = [i for i in self._insights if i.severity != "info"][:20]
        for ins in shown:
            icon = sev_icons.get(ins.severity, "??")
            color = sev_colors.get(ins.severity, "#6B7280")
            item = QTreeWidgetItem([icon, ins.title])
            item.setForeground(0, QBrush(QColor(color)))
            item.setForeground(1, QBrush(QColor(color)))
            item.setToolTip(1, ins.description)
            self.list_w.addTopLevelItem(item)

        self.list_w.resizeColumnToContents(0)


# ─── AI Relationship Predictor ───────────────────────────────────────────
class AIRelationshipPredictor:
    """
    Analyzes the family tree and suggests likely missing connections
    based on surname matching, generation proximity, and date patterns.
    """

    def __init__(self, model: FamilyTreeModel):
        self.model = model

    def _extract_surname(self, name: str) -> str:
        parts = name.strip().split()
        return parts[-1].lower() if parts else ""

    def _get_generation(self, pid: str) -> int:
        """Get generation level using BFS."""
        roots = self.model.get_roots()
        gens: dict[str, int] = {r: 0 for r in roots}
        q: deque[str] = deque(list(roots))
        visited: set[str] = set()
        while q:
            cur = q.popleft()
            if cur in visited:
                continue
            visited.add(cur)
            g = gens.get(cur, 0)
            for c in self.model.get_children(cur):
                ng = g + 1
                gens[c] = ng if c not in gens else max(gens[c], ng)
                if c not in visited:
                    q.append(c)
            for s in self.model.get_spouses(cur):
                if s not in gens:
                    gens[s] = g
                if s not in visited:
                    q.append(s)
        return gens.get(pid, -1)

    def predict(self) -> list[Insight]:
        """Generate relationship predictions."""
        insights: list[Insight] = []
        if len(self.model.persons) < 3:
            return insights

        names = {pid: p.name for pid, p in self.model.persons.items()}
        surnames: dict[str, list[str]] = {}  # surname_lower -> [pid, ...]
        for pid, p in self.model.persons.items():
            sn = self._extract_surname(p.name)
            if sn:
                surnames.setdefault(sn, []).append(pid)

        # Suggestion 1: Same surname, same generation, not connected
        gen_cache: dict[str, int] = {}
        for pid in self.model.persons:
            gen_cache[pid] = self._get_generation(pid)

        for sn, pids in surnames.items():
            if len(pids) < 2:
                continue
            for i in range(len(pids)):
                for j in range(i + 1, len(pids)):
                    a, b = pids[i], pids[j]
                    # Check if already related
                    already = (
                        b in self.model.get_parents(a) or a in self.model.get_parents(b) or
                        b in self.model.get_children(a) or a in self.model.get_children(b) or
                        b in self.model.get_spouses(a) or a in self.model.get_spouses(b)
                    )
                    if not already:
                        ga, gb = gen_cache.get(a, -1), gen_cache.get(b, -1)
                        # Same generation: could be siblings or spouses
                        if ga == gb and ga >= 0:
                            # Check if they share a parent (already siblings)
                            parents_a = set(self.model.get_parents(a))
                            parents_b = set(self.model.get_parents(b))
                            if not (parents_a & parents_b):
                                insights.append(Insight(
                                    severity="suggestion",
                                    category="relationship",
                                    title=f"Possible siblings: {names[a]} & {names[b]}",
                                    description=f"Same surname '{sn}', same generation ({ga + 1}), "
                                                f"not connected. They may be siblings or cousins.",
                                    person_ids=[a, b],
                                ))

        # Suggestion 2: Unmarried children of married parents — suggest spouse
        for pid, p in self.model.persons.items():
            if p.death_date and not p.birth_date:
                continue
            by = _parse_year(p.birth_date)
            if by is None:
                continue
            age = (2026 - by) if not p.death_date else None
            if age is not None and 25 <= age <= 75 and not p.death_date:
                if not self.model.get_spouses(pid) and not self.model.get_children(pid):
                    insights.append(Insight(
                        severity="suggestion",
                        category="relationship",
                        title=f"Possible spouse missing: {p.name}",
                        description=f"{p.name} is {age} years old, alive, with no spouse or children recorded.",
                        person_ids=[pid],
                    ))

        return insights


# ─── Scene ────────────────────────────────────────────────────────────────────
class FamilyTreeScene(QGraphicsScene):
    edit_person_requested = Signal(str); delete_person_requested = Signal(str); selection_changed_sig = Signal(str)
    relationship_created = Signal(str, str, str)  # rel_type, id1, id2
    duplicate_person_requested = Signal(str)
    remove_relationship_requested = Signal(str)
    disconnect_person_requested = Signal(str)
    select_connected_requested = Signal(str, str)  # pid, mode ("children"/"spouses"/"all")
    rename_person_requested = Signal(str)
    copy_person_requested = Signal(str)  # Ctrl+C
    paste_person_requested = Signal()   # Ctrl+V

    def __init__(self, model: FamilyTreeModel):
        super().__init__()
        self.model = model; self.nodes: dict[str, PersonNode] = {}; self.brackets: list[FamilyBracket] = []
        self.spouse_links: list[SpouseLink] = []; self.gen_levels: dict[str, int] = {}
        self._animating = False; self._anim_timer = QTimer(); self._anim_timer.setInterval(16); self._anim_timer.timeout.connect(self._anim_step)
        self._anim_start: dict[str, QPointF] = {}; self._anim_target: dict[str, QPointF] = {}; self._anim_progress = 0.0
        self._drag_src = None; self._drag_line = None
        self.setBackgroundBrush(QBrush(C["bg"])); self.selectionChanged.connect(self._sel_changed)

    def _sel_changed(self):
        sel = self.selectedItems(); pid = ""
        if sel and isinstance(sel[0], PersonNode): pid = sel[0].person.id
        self.selection_changed_sig.emit(pid); self._highlight_connections(pid)

    def _highlight_connections(self, pid: str):
        for br in self.brackets: pids = {n.person.id for n in br.parent_nodes + br.child_nodes}; br.setHighlighted(pid in pids)
        for sl in self.spouse_links: pids = {sl.node1.person.id, sl.node2.person.id}; sl.setHighlighted(pid in pids)
        for nid, node in self.nodes.items(): node.setHighlight(nid == pid)

    def drawBackground(self, painter: QPainter, rect: QRectF):
        super().drawBackground(painter, rect); gs = 25; painter.setPen(QPen(C["grid"], 1.2, Qt.RoundCap))
        left, top = int(rect.left()) - int(rect.left()) % gs, int(rect.top()) - int(rect.top()) % gs
        pts = []
        x = left
        while x < rect.right():
            y = top
            while y < rect.bottom():
                pts.append(QPointF(x, y))
                y += gs
            x += gs
        if pts:
            painter.drawPoints(pts)
        if self.gen_levels:
            gen_y: dict[int, float] = {}
            for pid, gen in self.gen_levels.items():
                if pid in self.nodes: y = self.nodes[pid].pos().y() + NODE_H / 2; gen_y[gen] = y if gen not in gen_y else min(gen_y[gen], y)
            painter.setFont(QFont("Segoe UI", 9, QFont.Medium)); painter.setPen(C["gen_lbl"])
            for gen in sorted(gen_y.keys()):
                y = gen_y[gen]
                if rect.top() <= y <= rect.bottom(): painter.drawText(QPointF(rect.left() + 8, y + 4), f"Gen {gen + 1}")

    def rebuild(self):
        self.clear(); self.nodes.clear(); self.brackets.clear(); self.spouse_links.clear()
        for pid, p in self.model.persons.items(): n = PersonNode(p); self.addItem(n); self.nodes[pid] = n
        for parent_ids, child_ids in self.model.get_family_units():
            pn = [self.nodes[pid] for pid in parent_ids if pid in self.nodes]; cn = [self.nodes[cid] for cid in child_ids if cid in self.nodes]
            if pn and cn: br = FamilyBracket(pn, cn); self.addItem(br); self.brackets.append(br)
        for a, b in self.model.spouses:
            if a in self.nodes and b in self.nodes: sl = SpouseLink(self.nodes[a], self.nodes[b]); self.addItem(sl); self.spouse_links.append(sl)

    def update_connectors(self):
        for br in self.brackets: br.update_path()
        for sl in self.spouse_links: sl.update_path()

    def auto_layout(self, animate=True):
        positions = self._compute_layout(); self._compute_gen_levels()
        if not animate:
            for pid, pos in positions.items():
                if pid in self.nodes: self.nodes[pid].setPos(pos)
            self.update_connectors(); return
        self._anim_start = {pid: self.nodes[pid].pos() for pid in positions if pid in self.nodes}
        self._anim_target = {pid: pos for pid, pos in positions.items() if pid in self.nodes}
        self._anim_progress = 0.0; self._animating = True; self._anim_timer.start()

    def _anim_step(self):
        self._anim_progress += 0.06
        if self._anim_progress >= 1.0: self._anim_progress = 1.0; self._anim_timer.stop(); self._animating = False
        t = 1 - (1 - self._anim_progress) ** 3
        for pid in list(self._anim_start):
            if pid not in self.nodes or pid not in self._anim_target:
                continue
            s, e = self._anim_start[pid], self._anim_target[pid]; self.nodes[pid].setPos(s + (e - s) * t)
        self.update_connectors()

    def _bfs_gen_levels(self) -> dict[str, int]:
        """Shared BFS that assigns generation levels to every reachable person."""
        gens: dict[str, int] = {}; roots = self.model.get_roots(); q: deque[str] = deque()
        for r in roots: gens[r] = 0; q.append(r)
        visited: set[str] = set()
        while q:
            cur = q.popleft()
            if cur in visited:
                continue
            visited.add(cur)
            g = gens[cur]
            for c in self.model.get_children(cur):
                ng = g + 1; gens[c] = ng if c not in gens else max(gens[c], ng)
                if c not in visited: q.append(c)
            for s in self.model.get_spouses(cur):
                if s not in gens: gens[s] = g
                if s not in visited: q.append(s)
        return gens

    def _compute_gen_levels(self):
        self.gen_levels = self._bfs_gen_levels()

    def _compute_layout(self) -> dict[str, QPointF]:
        if not self.model.persons: return {}
        gens = self._bfs_gen_levels()
        _cache: dict[str, float] = {}
        def _width(pid: str) -> float:
            if pid in _cache: return _cache[pid]
            sp = self.model.get_spouses(pid); fam = [pid] + sp; fw = len(fam) * NODE_W + max(0, len(fam) - 1) * SPOUSE_GAP
            ch = self.model.get_family_children(fam)
            if not ch: _cache[pid] = fw; return fw
            cw = sum(_width(c) for c in ch) + (len(ch) - 1) * H_GAP; res = max(fw, cw); _cache[pid] = res; return res

        positions: dict[str, QPointF] = {}; visited: set[str] = set()
        def _place(pid: str, cx: float, y: float):
            if pid in visited: return
            visited.add(pid); sp = [s for s in self.model.get_spouses(pid) if s not in visited]
            for s in sp: visited.add(s)
            fam = [pid] + sp; fw = len(fam) * NODE_W + max(0, len(fam) - 1) * SPOUSE_GAP; fx = cx - fw / 2
            for i, fid in enumerate(fam): positions[fid] = QPointF(fx + i * (NODE_W + SPOUSE_GAP), y)
            ch = [c for c in self.model.get_family_children(fam) if c not in visited]
            if not ch: return
            cwidths = [_width(c) for c in ch]; total = sum(cwidths) + (len(ch) - 1) * H_GAP; sx = cx - total / 2; cy = y + NODE_H + V_GAP
            for i, cid in enumerate(ch): _place(cid, sx + cwidths[i] / 2, cy); sx += cwidths[i] + H_GAP

        rvisited: set[str] = set(); rfamilies: list[list[str]] = []
        for r in roots:
            if r in rvisited: continue
            fam = [r] + [s for s in self.model.get_spouses(r) if s not in rvisited]; rvisited.update(fam); rfamilies.append(fam)
        for pid in self.model.persons:
            if pid not in rvisited: rfamilies.append([pid]); rvisited.add(pid)
        rwidths = [_width(f[0]) for f in rfamilies]; total_w = sum(rwidths) + (len(rfamilies) - 1) * H_GAP; cx = -total_w / 2
        for fam, w in zip(rfamilies, rwidths): _place(fam[0], cx + w / 2, 0); cx += w + H_GAP
        for pid in self.model.persons:
            if pid not in positions: positions[pid] = QPointF(len(positions) * (NODE_W + H_GAP), gens.get(pid, 0) * (NODE_H + V_GAP))
        return positions

    # ── Drag-to-Connect ────────────────────────────────────────────────────
    def mousePressEvent(self, ev):
        if ev.button() == Qt.LeftButton and ev.modifiers() & Qt.ShiftModifier:
            item = self.itemAt(ev.scenePos(), QTransform())
            if isinstance(item, PersonNode):
                self._drag_src = item
                self._drag_line = QGraphicsLineItem(
                    QLineF(item.pos() + QPointF(NODE_W / 2, NODE_H / 2),
                            item.pos() + QPointF(NODE_W / 2, NODE_H / 2)))
                self._drag_line.setPen(QPen(C["conn_hi"], 2, Qt.DashLine))
                self._drag_line.setZValue(100)
                self.addItem(self._drag_line)
                ev.accept(); return
        self._drag_src = None
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        if self._drag_src is not None and self._drag_line is not None:
            src_pos = self._drag_src.pos() + QPointF(NODE_W / 2, NODE_H / 2)
            self._drag_line.setLine(QLineF(src_pos, ev.scenePos()))
            ev.accept(); return
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        if self._drag_src is not None and self._drag_line is not None:
            if self._drag_line.scene() is not None:
                self.removeItem(self._drag_line)
            self._drag_line = None
            target = self.itemAt(ev.scenePos(), QTransform())
            if isinstance(target, PersonNode) and target is not self._drag_src:
                src_id = self._drag_src.person.id
                tgt_id = target.person.id
                # Ask user what kind of relationship
                menu = QMenu()
                a_pc = menu.addAction(f"Parent-Child: {self._drag_src.person.name} → {target.person.name}")
                a_sp = menu.addAction(f"Spouse: {self._drag_src.person.name} & {target.person.name}")
                act = menu.exec(ev.screenPos())
                if act == a_pc:
                    self.relationship_created.emit("pc", src_id, tgt_id)
                elif act == a_sp:
                    self.relationship_created.emit("spouse", src_id, tgt_id)
            self._drag_src = None
            ev.accept(); return
        self._drag_src = None
        super().mouseReleaseEvent(ev)

    def contextMenuEvent(self, ev):
        item = self.itemAt(ev.scenePos(), QTransform()); menu = QMenu()
        if isinstance(item, PersonNode):
            pid = item.person.id
            a_edit = menu.addAction("✏️  Edit")
            a_del = menu.addAction("🗑️  Delete")
            a_dup = menu.addAction("📋  Duplicate")
            menu.addSeparator()
            a_child = menu.addAction("👶  Add Child")
            a_spouse = menu.addAction("💍  Add Spouse")
            a_parent = menu.addAction("⬆️  Add Parent")
            menu.addSeparator()
            sub_select = menu.addMenu("🖱️  Select Connected")
            a_sel_ch = sub_select.addAction("Select Children")
            a_sel_sp = sub_select.addAction("Select Spouses")
            a_sel_all = sub_select.addAction("Select All Related")
            menu.addSeparator()
            a_remove_rel = menu.addAction("✂️  Remove Relationship…")
            a_disconnect = menu.addAction("🔗  Disconnect All")
            act = menu.exec(ev.screenPos())
            if act == a_edit: self.edit_person_requested.emit(pid)
            elif act == a_del: self.delete_person_requested.emit(pid)
            elif act == a_dup: self.duplicate_person_requested.emit(pid)
            elif act == a_child: self._quick_add_child(pid)
            elif act == a_spouse: self._quick_add_spouse(pid)
            elif act == a_parent: self._quick_add_parent(pid)
            elif act == a_sel_ch: self.select_connected_requested.emit(pid, "children")
            elif act == a_sel_sp: self.select_connected_requested.emit(pid, "spouses")
            elif act == a_sel_all: self.select_connected_requested.emit(pid, "all")
            elif act == a_remove_rel: self.remove_relationship_requested.emit(pid)
            elif act == a_disconnect: self.disconnect_person_requested.emit(pid)
        else:
            a_add = menu.addAction("➕  Add Person"); a_lay = menu.addAction("🔄  Auto Layout")
            menu.addSeparator(); menu.addAction("Shift+Drag between nodes to connect").setEnabled(False)
            act = menu.exec(ev.screenPos())
            if act == a_add: self._quick_add_person()
            elif act == a_lay: self.auto_layout()

    def _quick_add_person(self):
        dlg = PersonDialog(parent=self.views()[0])
        if dlg.exec() == QDialog.Accepted:
            p = dlg.get_person()
            if p.name: self.model.add_person(p); self.rebuild(); self.auto_layout()

    def _quick_add_child(self, pid):
        dlg = PersonDialog(parent=self.views()[0])
        if dlg.exec() == QDialog.Accepted:
            p = dlg.get_person()
            if p.name: self.model.add_person(p); self.model.add_parent_child(pid, p.id); self.rebuild(); self.auto_layout()

    def _quick_add_spouse(self, pid):
        dlg = PersonDialog(parent=self.views()[0])
        if dlg.exec() == QDialog.Accepted:
            p = dlg.get_person()
            if p.name: self.model.add_person(p); self.model.add_spouse(pid, p.id); self.rebuild(); self.auto_layout()

    def _quick_add_parent(self, pid):
        dlg = PersonDialog(parent=self.views()[0])
        if dlg.exec() == QDialog.Accepted:
            p = dlg.get_person()
            if p.name: self.model.add_person(p); self.model.add_parent_child(p.id, pid); self.rebuild(); self.auto_layout()


# ─── View ─────────────────────────────────────────────────────────────────────
class FamilyTreeView(QGraphicsView):
    delete_requested = Signal()
    def __init__(self, scene: FamilyTreeScene, parent=None):
        super().__init__(scene, parent)
        self.setRenderHint(QPainter.Antialiasing); self.setRenderHint(QPainter.SmoothPixmapTransform)
        self.setDragMode(QGraphicsView.RubberBandDrag); self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setViewportUpdateMode(QGraphicsView.FullViewportUpdate); self.setContextMenuPolicy(Qt.NoContextMenu)

    def wheelEvent(self, ev):
        f = 1.15 if ev.angleDelta().y() > 0 else 1 / 1.15
        if 0.08 < self.transform().m11() * f < 8.0: self.scale(f, f)

    def keyPressEvent(self, ev):
        if ev.key() == Qt.Key_Delete: self.delete_requested.emit(); return
        if ev.key() == Qt.Key_F2:
            # Forward F2 to the focused PersonNode
            focus = self.scene().focusItem()
            if focus and isinstance(focus, PersonNode):
                focus.keyPressEvent(ev)
            return
        if ev.modifiers() & Qt.ControlModifier and ev.key() == Qt.Key_C:
            sel = [i for i in self.scene().selectedItems() if isinstance(i, PersonNode)]
            if sel and hasattr(self.scene(), 'copy_person_requested'):
                self.scene().copy_person_requested.emit(sel[0].person.id)
            return
        if ev.modifiers() & Qt.ControlModifier and ev.key() == Qt.Key_V:
            if hasattr(self.scene(), 'paste_person_requested'):
                self.scene().paste_person_requested.emit()
            return
        super().keyPressEvent(ev)

    def drawForeground(self, painter, rect):
        zoom = int(self.transform().m11() * 100); painter.save(); painter.resetTransform()
        w, h = self.viewport().width(), self.viewport().height()
        painter.setFont(QFont("Segoe UI", 9)); painter.setPen(C["text3"]); painter.drawText(w - 60, h - 12, f"{zoom}%"); painter.restore()


# ─── Charts & Stats Dialog ───────────────────────────────────────────────────
class StatsDialog(QDialog):
    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent)
        self.model = model
        self.setWindowTitle("Family Tree Statistics & Charts")
        self.setMinimumSize(950, 750)
        lay = QVBoxLayout(self)

        tabs = QTabWidget()
        tabs.addTab(self._create_overview_tab(), "Overview")
        tabs.addTab(self._create_charts_tab(), "Charts")
        lay.addWidget(tabs)

        btn_box = QHBoxLayout()
        export_btn = QPushButton("Export Charts to PNG")
        export_btn.setObjectName("accentBtn")
        export_btn.clicked.connect(self._export_charts)
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.close)
        btn_box.addStretch()
        btn_box.addWidget(export_btn)
        btn_box.addWidget(close_btn)
        lay.addLayout(btn_box)

    def _get_generations(self):
        gens = {}
        roots = self.model.get_roots()
        q = deque(roots)
        for r in roots: gens[r] = 0
        visited: set[str] = set()
        while q:
            cur = q.popleft()
            if cur in visited:
                continue
            visited.add(cur)
            g = gens[cur]
            for c in self.model.get_children(cur):
                ng = g + 1
                if c not in gens or gens[c] < ng: gens[c] = ng
                if c not in visited: q.append(c)
            for s in self.model.get_spouses(cur):
                if s not in gens: gens[s] = g
                if s not in visited: q.append(s)
        return gens

    def _create_overview_tab(self) -> QWidget:
        w = QWidget(); lay = QVBoxLayout(w)
        total = len(self.model.persons)
        males = sum(1 for p in self.model.persons.values() if p.gender == "Male")
        females = sum(1 for p in self.model.persons.values() if p.gender == "Female")
        others = total - males - females
        alive = sum(1 for p in self.model.persons.values() if not p.death_date)
        deceased = total - alive
        families = len(self.model.get_family_units())
        marriages = len(self.model.spouses)
        gens = self._get_generations()
        max_gen = max(gens.values()) + 1 if gens else 0

        # Compute average age of deceased
        ages = []
        for p in self.model.persons.values():
            by = _parse_year(p.birth_date)
            dy = _parse_year(p.death_date)
            if by is not None and dy is not None:
                ages.append(dy - by)
        avg_age = f"{sum(ages) / len(ages):.1f}" if ages else "N/A"
        oldest = str(max(ages)) if ages else "N/A"

        info = QGroupBox("Tree Summary"); info.setStyleSheet("QGroupBox { font-weight: bold; }")
        il = QFormLayout(info)
        il.addRow("Total Members:", QLabel(str(total)))
        il.addRow("Generations:", QLabel(str(max_gen)))
        il.addRow("Family Units:", QLabel(str(families)))
        il.addRow("Marriages:", QLabel(str(marriages)))
        il.addRow("", QLabel(""))
        il.addRow("Male:", QLabel(str(males)))
        il.addRow("Female:", QLabel(str(females)))
        il.addRow("Other:", QLabel(str(others)))
        il.addRow("", QLabel(""))
        il.addRow("Alive:", QLabel(str(alive)))
        il.addRow("Deceased:", QLabel(str(deceased)))
        il.addRow("Avg Age (deceased):", QLabel(avg_age))
        il.addRow("Oldest (deceased):", QLabel(oldest + (" years" if oldest != "N/A" else "")))
        lay.addWidget(info)
        lay.addStretch()
        return w

    def _create_charts_tab(self) -> QWidget:
        w = QWidget(); lay = QHBoxLayout(w)
        
        self.fig = Figure(figsize=(11, 8), facecolor=MC["bg"])
        self.canvas = FigureCanvas(self.fig)
        lay.addWidget(self.canvas)
        
        self._draw_charts()
        return w

    def _draw_charts(self):
        self.fig.clear()
        if not self.model.persons: return

        males = sum(1 for p in self.model.persons.values() if p.gender == "Male")
        females = sum(1 for p in self.model.persons.values() if p.gender == "Female")
        others = len(self.model.persons) - males - females
        alive = sum(1 for p in self.model.persons.values() if not p.death_date)
        deceased = len(self.model.persons) - alive

        # Chart 1: Gender Distribution (top-left)
        ax1 = self.fig.add_subplot(221)
        labels, sizes, colors = [], [], []
        if males: labels.append("Male"); sizes.append(males); colors.append(MC["male"])
        if females: labels.append("Female"); sizes.append(females); colors.append(MC["female"])
        if others: labels.append("Other"); sizes.append(others); colors.append(MC["other"])
        if sizes:
            ax1.pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%', startangle=90, textprops={'color': MC["text"], 'fontsize': 8})
        ax1.set_title("Gender Distribution", color=MC["text"], fontsize=10, pad=12)

        # Chart 2: Alive vs Deceased (top-right)
        ax2 = self.fig.add_subplot(222)
        if alive or deceased:
            ax2.pie([alive, deceased], labels=["Alive", "Deceased"], colors=[MC["alive"], MC["deceased"]],
                    autopct='%1.1f%%', startangle=90, textprops={'color': MC["text"], 'fontsize': 8})
        ax2.set_title("Alive vs Deceased", color=MC["text"], fontsize=10, pad=12)

        # Chart 3: Members per Generation (bottom-left)
        ax3 = self.fig.add_subplot(223)
        gens = self._get_generations()
        if gens:
            gen_counts = {}
            for g in gens.values(): gen_counts[g] = gen_counts.get(g, 0) + 1
            x = [f"Gen {g+1}" for g in sorted(gen_counts.keys())]
            y = [gen_counts[g] for g in sorted(gen_counts.keys())]
            bar_colors = [MC["male"], MC["female"]] * ((len(x) + 1) // 2)
            bars = ax3.bar(x, y, color=bar_colors[:len(x)], width=0.6)
            ax3.set_title("Members per Generation", color=MC["text"], fontsize=10, pad=12)
            ax3.tick_params(colors=MC["text"], labelsize=8)
            ax3.spines['top'].set_visible(False)
            ax3.spines['right'].set_visible(False)
            ax3.spines['bottom'].set_color(MC["grid"])
            ax3.spines['left'].set_color(MC["grid"])
            for bar in bars:
                ax3.text(bar.get_x() + bar.get_width()/2., bar.get_height(), str(int(bar.get_height())),
                          ha='center', va='bottom', color=MC["text"], fontsize=8)

        # Chart 4: Age Distribution (bottom-right)
        ax4 = self.fig.add_subplot(224)
        death_ages = []
        for p in self.model.persons.values():
            by = _parse_year(p.birth_date)
            dy = _parse_year(p.death_date)
            if by is not None and dy is not None and dy >= by:
                death_ages.append(dy - by)
        if death_ages:
            bins = range(min(death_ages), max(death_ages) + 10, 10)
            ax4.hist(death_ages, bins=bins, color=MC["male"], edgecolor=MC["bg"], alpha=0.85)
            ax4.axvline(sum(death_ages) / len(death_ages), color=MC["deceased"], linestyle='--', linewidth=1.5, label='Average')
            ax4.set_title("Age at Death Distribution", color=MC["text"], fontsize=10, pad=12)
            ax4.set_xlabel("Age", color=MC["text"], fontsize=8)
            ax4.set_ylabel("Count", color=MC["text"], fontsize=8)
            ax4.tick_params(colors=MC["text"], labelsize=8)
            ax4.spines['top'].set_visible(False)
            ax4.spines['right'].set_visible(False)
            ax4.spines['bottom'].set_color(MC["grid"])
            ax4.spines['left'].set_color(MC["grid"])
            ax4.legend(fontsize=8, facecolor=MC["bg"], edgecolor=MC["grid"], labelcolor=MC["text"])
        else:
            ax4.text(0.5, 0.5, "No deceased members\nwith valid dates", transform=ax4.transAxes,
                     ha='center', va='center', color=MC["text3"], fontsize=10)
            ax4.set_title("Age at Death Distribution", color=MC["text"], fontsize=10, pad=12)

        self.fig.tight_layout(pad=2.5)
        self.canvas.draw()

    def _export_charts(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export Charts as PNG", "", "PNG (*.png)")
        if path:
            try:
                self.fig.savefig(path, dpi=300, bbox_inches='tight', facecolor=self.fig.get_facecolor())
                QMessageBox.information(self, "Success", f"Charts exported successfully to:\n{path}")
            except Exception as e:
                QMessageBox.critical(self, "Error", str(e))


# ─── Dialogs ──────────────────────────────────────────────────────────────────
class PersonDialog(QDialog):
    def __init__(self, person: Person | None = None, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Edit Person" if person else "Add Person"); self.setMinimumWidth(400)
        lay = QFormLayout(self)
        self.name_ed = QLineEdit(person.name if person else "")
        self.gender_cb = QComboBox(); self.gender_cb.addItems(["Male", "Female", "Other"])
        if person: idx = self.gender_cb.findText(person.gender); self.gender_cb.setCurrentIndex(idx if idx >= 0 else 0)
        self.birth_ed = QLineEdit(person.birth_date if person else ""); self.birth_ed.setPlaceholderText("e.g. 1965 or 1965-03-15")
        self.death_ed = QLineEdit(person.death_date if person else ""); self.death_ed.setPlaceholderText("Leave empty if alive")
        self.notes_ed = QTextEdit(person.notes if person else ""); self.notes_ed.setMaximumHeight(80)
        lay.addRow("Name *:", self.name_ed); lay.addRow("Gender:", self.gender_cb); lay.addRow("Birth:", self.birth_ed); lay.addRow("Death:", self.death_ed); lay.addRow("Notes:", self.notes_ed)
        btns = QHBoxLayout(); ok = QPushButton("Save"); ok.setObjectName("accentBtn"); ok.clicked.connect(self.accept); cancel = QPushButton("Cancel"); cancel.clicked.connect(self.reject)
        ok.setDefault(True); btns.addWidget(ok); btns.addWidget(cancel); lay.addRow(btns)

    def get_person(self) -> Person:
        return Person(name=self.name_ed.text().strip(), gender=self.gender_cb.currentText(), birth_date=self.birth_ed.text().strip(), death_date=self.death_ed.text().strip(), notes=self.notes_ed.toPlainText().strip())


class RelationshipDialog(QDialog):
    def __init__(self, model: FamilyTreeModel, kind="parent_child", preselect_id="", parent=None):
        super().__init__(parent); self.model = model; self.kind = kind
        self.setWindowTitle("Add Parent → Child" if kind == "parent_child" else "Add Spouse"); self.setMinimumWidth(340)
        lay = QFormLayout(self); names = {pid: p.name for pid, p in model.persons.items()}; self.cb1 = QComboBox(); self.cb2 = QComboBox()
        for pid, nm in names.items(): self.cb1.addItem(nm, pid); self.cb2.addItem(nm, pid)
        if preselect_id: idx1 = self.cb1.findData(preselect_id); self.cb1.setCurrentIndex(idx1 if idx1 >= 0 else 0)
        if kind == "parent_child":
            lay.addRow("Parent:", self.cb1); lay.addRow("Child:", self.cb2)
            if preselect_id: idx2 = self.cb2.findData(preselect_id); self.cb2.setCurrentIndex(idx2 if idx2 >= 0 else 0)
        else: lay.addRow("Person 1:", self.cb1); lay.addRow("Person 2:", self.cb2)
        btns = QHBoxLayout(); ok = QPushButton("Connect"); ok.setObjectName("accentBtn"); ok.clicked.connect(self.accept); cancel = QPushButton("Cancel"); cancel.clicked.connect(self.reject)
        ok.setDefault(True); btns.addWidget(ok); btns.addWidget(cancel); lay.addRow(btns)

    def get_ids(self): return self.cb1.currentData(), self.cb2.currentData()


# ─── Path Finder Dialog ───────────────────────────────────────────────────
# ─── Remove Relationship Dialog ──────────────────────────────────────────
class RemoveRelationshipDialog(QDialog):
    """Dialog showing all relationships of a person, allowing the user to remove one."""
    def __init__(self, model: FamilyTreeModel, pid: str, parent=None):
        super().__init__(parent)
        self.model = model
        self.pid = pid
        self._relations: list[tuple[str, str, str]] = []  # (rel_type, id1, id2)
        person = model.persons[pid]
        self.setWindowTitle(f"Relationships — {person.name}")
        self.setMinimumWidth(420)
        self.setMinimumHeight(300)
        lay = QVBoxLayout(self)

        info = QLabel(f"Relationships involving <b>{person.name}</b>:")
        info.setStyleSheet("margin-bottom: 6px;")
        lay.addWidget(info)

        self.rel_list = QTreeWidget()
        self.rel_list.setHeaderLabels(["Type", "Person", "Direction"])
        self.rel_list.setRootIsDecorated(False)
        self.rel_list.setAlternatingRowColors(True)
        lay.addWidget(self.rel_list)

        self._populate()

        btns = QHBoxLayout()
        self.b_remove = QPushButton("Remove Selected")
        self.b_remove.setObjectName("accentBtn")
        self.b_remove.clicked.connect(self._remove_selected)
        self.b_remove.setEnabled(False)
        self.b_disconnect_all = QPushButton("Disconnect All")
        self.b_disconnect_all.clicked.connect(self._disconnect_all)
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.reject)
        btns.addWidget(self.b_remove)
        btns.addWidget(self.b_disconnect_all)
        btns.addStretch()
        btns.addWidget(close_btn)
        lay.addLayout(btns)

        self.rel_list.itemSelectionChanged.connect(
            lambda: self.b_remove.setEnabled(bool(self.rel_list.selectedItems())))

    def _populate(self):
        self.rel_list.clear()
        self._relations.clear()
        pid = self.pid
        names = {p_id: p.name for p_id, p in self.model.persons.items()}

        # Parent relationships (pid is the child)
        for parent_id in self.model.get_parents(pid):
            if parent_id in names:
                it = QTreeWidgetItem(["Parent-Child", names[parent_id], f"{names[parent_id]} is parent of {names[pid]}"])
                it.setData(0, Qt.UserRole, ("pc", parent_id, pid))
                self.rel_list.addTopLevelItem(it)
                self._relations.append(("pc", parent_id, pid))

        # Child relationships (pid is the parent)
        for child_id in self.model.get_children(pid):
            if child_id in names:
                it = QTreeWidgetItem(["Parent-Child", names[child_id], f"{names[pid]} is parent of {names[child_id]}"])
                it.setData(0, Qt.UserRole, ("pc", pid, child_id))
                self.rel_list.addTopLevelItem(it)
                self._relations.append(("pc", pid, child_id))

        # Spouse relationships
        for spouse_id in self.model.get_spouses(pid):
            if spouse_id in names:
                it = QTreeWidgetItem(["Spouse", names[spouse_id], "Spouses"])
                it.setData(0, Qt.UserRole, ("spouse", pid, spouse_id))
                self.rel_list.addTopLevelItem(it)
                self._relations.append(("spouse", pid, spouse_id))

        for i in range(3):
            self.rel_list.resizeColumnToContents(i)

    def _remove_selected(self):
        items = self.rel_list.selectedItems()
        if not items:
            return
        item = items[0]
        data = item.data(0, Qt.UserRole)
        if data:
            self._removed = data  # (rel_type, id1, id2)
            self.accept()

    def _disconnect_all(self):
        if not self._relations:
            return
        self._removed = ("disconnect_all", self.pid, "")
        self.accept()

    def get_removed(self):
        return getattr(self, '_removed', None)


class PathFinderDialog(QDialog):
    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent)
        self.model = model
        self.setWindowTitle("Find Relationship Path")
        self.setMinimumWidth(380)
        lay = QVBoxLayout(self)
        info = QLabel("Select two people to find the shortest relationship path between them.")
        info.setWordWrap(True); info.setStyleSheet("color: #6B7280; margin-bottom: 8px;"); lay.addWidget(info)
        fl = QFormLayout()
        names = {pid: p.name for pid, p in model.persons.items()}
        self.cb1 = QComboBox(); self.cb2 = QComboBox()
        for pid, nm in sorted(names.items(), key=lambda x: x[1]):
            self.cb1.addItem(nm, pid); self.cb2.addItem(nm, pid)
        fl.addRow("Person A:", self.cb1); fl.addRow("Person B:", self.cb2)
        lay.addLayout(fl)
        self.result_label = QLabel(""); self.result_label.setWordWrap(True)
        self.result_label.setStyleSheet("padding: 10px; background: #F0F9FF; border-radius: 6px; margin-top: 8px;")
        lay.addWidget(self.result_label)
        btns = QHBoxLayout()
        find_btn = QPushButton("Find Path"); find_btn.setObjectName("accentBtn"); find_btn.clicked.connect(self._find)
        swap_btn = QPushButton("Swap"); swap_btn.clicked.connect(self._swap)
        ok = QPushButton("Highlight in Tree"); ok.setObjectName("accentBtn"); ok.clicked.connect(self.accept)
        cancel = QPushButton("Cancel"); cancel.clicked.connect(self.reject)
        btns.addWidget(find_btn); btns.addWidget(swap_btn); btns.addStretch(); btns.addWidget(ok); btns.addWidget(cancel)
        lay.addLayout(btns)

    def _swap(self):
        i1, i2 = self.cb1.currentIndex(), self.cb2.currentIndex()
        self.cb1.setCurrentIndex(i2); self.cb2.setCurrentIndex(i1)
        self._find()

    def _find(self):
        a, b = self.cb1.currentData(), self.cb2.currentData()
        if not a or not b:
            self.result_label.setText(""); return
        if a == b:
            self.result_label.setText("Same person selected."); return
        path = _find_path(self.model, a, b)
        if path is None:
            self.result_label.setText(f"No relationship path found between '{self.cb1.currentText()}' and '{self.cb2.currentText()}'.")
            self.result_label.setStyleSheet("padding: 10px; background: #FEF2F2; border-radius: 6px; margin-top: 8px; color: #991B1B;")
        else:
            parts = []
            names = {pid: p.name for pid, p in self.model.persons.items()}
            for i in range(len(path) - 1):
                x, y = path[i], path[i + 1]
                if y in self.model.get_children(x):
                    rel = "parent of"
                elif x in self.model.get_children(y):
                    rel = "child of"
                elif y in self.model.get_spouses(x):
                    rel = "spouse of"
                else:
                    rel = "related to"
                parts.append(f"{names.get(x, '?')} <b>({rel})</b> {names.get(y, '?')}")
            self.result_label.setText("Path (" + str(len(path)) + " people):<br><br>" + "<br>".join(parts))
            self.result_label.setStyleSheet("padding: 10px; background: #F0F9FF; border-radius: 6px; margin-top: 8px;")

    def get_ids(self):
        return self.cb1.currentData(), self.cb2.currentData()


# ─── Panels ───────────────────────────────────────────────────────────────────
class PropertiesPanel(QWidget):
    edit_requested = Signal(str); delete_requested = Signal(str)
    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent); self.model = model; self._pid: str | None = None
        lay = QVBoxLayout(self); lay.setContentsMargins(12, 12, 12, 12)
        self.title = QLabel("Details"); self.title.setFont(QFont("Segoe UI", 13, QFont.Medium)); self.title.setStyleSheet("color: #1F2937;"); lay.addWidget(self.title)
        g = QGroupBox("Information"); gl = QFormLayout(g)
        self.l_name = QLabel("-"); self.l_gender = QLabel("-"); self.l_birth = QLabel("-"); self.l_death = QLabel("-"); self.l_age = QLabel("-"); self.l_notes = QLabel("-"); self.l_notes.setWordWrap(True)
        gl.addRow("Name:", self.l_name); gl.addRow("Gender:", self.l_gender); gl.addRow("Birth:", self.l_birth); gl.addRow("Death:", self.l_death); gl.addRow("Age:", self.l_age); gl.addRow("Notes:", self.l_notes); lay.addWidget(g)
        rg = QGroupBox("Relationships"); rl = QVBoxLayout(rg); self.l_rel = QLabel("No selection"); self.l_rel.setWordWrap(True); rl.addWidget(self.l_rel); lay.addWidget(rg)
        btns = QHBoxLayout(); self.b_edit = QPushButton("Edit"); self.b_del = QPushButton("Delete"); self.b_edit.setEnabled(False); self.b_del.setEnabled(False)
        self.b_edit.clicked.connect(lambda: self.edit_requested.emit(self._pid or "")); self.b_del.clicked.connect(lambda: self.delete_requested.emit(self._pid or ""))
        btns.addWidget(self.b_edit); btns.addWidget(self.b_del); lay.addLayout(btns); lay.addStretch()

    def show_person(self, pid: str):
        self._pid = pid or None
        if not pid or pid not in self.model.persons:
            self.title.setText("Details"); [w.setText("-") for w in (self.l_name, self.l_gender, self.l_birth, self.l_death, self.l_age, self.l_notes)]; self.l_rel.setText("No selection"); self.b_edit.setEnabled(False); self.b_del.setEnabled(False); return
        p = self.model.persons[pid]; self.title.setText(p.name); self.l_name.setText(p.name); self.l_gender.setText(p.gender); self.l_birth.setText(p.birth_date or "Unknown"); self.l_death.setText(p.death_date or "Alive"); self.l_age.setText(_compute_age(p.birth_date, p.death_date)); self.l_notes.setText(p.notes or "None")
        lines = []
        if par := self.model.get_parents(pid): lines.append("Parents: " + ", ".join(self.model.persons[x].name for x in par if x in self.model.persons))
        if ch := self.model.get_children(pid): lines.append("Children: " + ", ".join(self.model.persons[x].name for x in ch if x in self.model.persons))
        if sp := self.model.get_spouses(pid): lines.append("Spouse(s): " + ", ".join(self.model.persons[x].name for x in sp if x in self.model.persons))
        self.l_rel.setText("\n".join(lines) if lines else "No relationships"); self.b_edit.setEnabled(True); self.b_del.setEnabled(True)


class MembersPanel(QWidget):
    member_selected = Signal(str)
    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent); self.model = model; self._all_items: list[tuple[str, QTreeWidgetItem]] = []
        lay = QVBoxLayout(self); lay.setContentsMargins(4, 4, 4, 4); header = QLabel("Members"); header.setFont(QFont("Segoe UI", 10, QFont.Medium)); lay.addWidget(header)
        self.search = QLineEdit(); self.search.setPlaceholderText("Search members..."); self.search.setClearButtonEnabled(True); self.search.textChanged.connect(self._apply_filter); lay.addWidget(self.search)
        self.tree = QTreeWidget(); self.tree.setHeaderLabels(["Name", "Born"]); self.tree.setAlternatingRowColors(True); self.tree.setRootIsDecorated(False); self.tree.itemClicked.connect(self._clicked); lay.addWidget(self.tree)

    def _clicked(self, item, _):
        if pid := item.data(0, Qt.UserRole): self.member_selected.emit(pid)

    def _apply_filter(self, text: str):
        query = text.lower().strip()
        for pid, item in self._all_items:
            match = not query or query in self.model.persons[pid].name.lower()
            item.setHidden(not match)

    def refresh(self):
        self.tree.clear(); self._all_items.clear()
        for pid, p in sorted(self.model.persons.items(), key=lambda x: x[1].name):
            it = QTreeWidgetItem([p.name, p.birth_date]); it.setData(0, Qt.UserRole, pid)
            if p.gender == "Male": it.setForeground(0, QBrush(C["male"]))
            elif p.gender == "Female": it.setForeground(0, QBrush(C["female"]))
            else: it.setForeground(0, QBrush(C["other"]))
            self.tree.addTopLevelItem(it); self._all_items.append((pid, it))
        for i in range(2): self.tree.resizeColumnToContents(i)
        self._apply_filter(self.search.text())


# ─── Main Window ──────────────────────────────────────────────────────────────
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Family Tree Creator"); self.resize(1500, 920)
        self.model = FamilyTreeModel(); self.is_dirty = False; self.current_file = ""
        self.undo_stack = QUndoStack(self)
        self._clipboard_person: Person | None = None  # for copy/paste

        self.scene = FamilyTreeScene(self.model)
        self.scene.edit_person_requested.connect(self.edit_person)
        self.scene.delete_person_requested.connect(self.delete_person)
        self.scene.relationship_created.connect(self._on_drag_relation)
        self.scene.duplicate_person_requested.connect(self.duplicate_person)
        self.scene.remove_relationship_requested.connect(self.remove_relationship)
        self.scene.disconnect_person_requested.connect(self.disconnect_person)
        self.scene.select_connected_requested.connect(self.select_connected)
        self.scene.rename_person_requested.connect(self.rename_person)
        self.scene.copy_person_requested.connect(self.copy_person)
        self.scene.paste_person_requested.connect(self.paste_person)
        self.view = FamilyTreeView(self.scene)
        self.view.delete_requested.connect(self.delete_selected)
        self.setCentralWidget(self.view)

        self.props = PropertiesPanel(self.model)
        self.props.edit_requested.connect(self.edit_person)
        self.props.delete_requested.connect(self.delete_person)
        self.scene.selection_changed_sig.connect(self.props.show_person)
        self.members = MembersPanel(self.model)
        self.members.member_selected.connect(self._focus_member)

        dock_r = QDockWidget("Properties", self); dock_r.setWidget(self.props); dock_r.setMinimumWidth(230); self.addDockWidget(Qt.RightDockWidgetArea, dock_r)
        dock_l = QDockWidget("Members", self); dock_l.setWidget(self.members); dock_l.setMinimumWidth(190); self.addDockWidget(Qt.LeftDockWidgetArea, dock_l)

        self.ai_panel = AISuggestionsPanel(self.model)
        dock_ai = QDockWidget("AI Suggestions", self); dock_ai.setWidget(self.ai_panel); dock_ai.setMinimumWidth(190)
        self.addDockWidget(Qt.LeftDockWidgetArea, dock_ai)

        self._build_actions(); self._build_toolbar(); self._build_menus()
        # Undo/Redo keyboard shortcuts
        QShortcut(QKeySequence.StandardKey.Undo, self, self.undo_stack.undo)
        QShortcut(QKeySequence.StandardKey.Redo, self, self.undo_stack.redo)
        self.undo_stack.cleanChanged.connect(lambda clean: self.set_dirty(not clean))
        self.statusBar().showMessage("Right-click to add/connect  |  Shift+Drag to connect  |  Ctrl+M MCTS optimize  |  Ctrl+Shift+A AI analyze  |  Ctrl+D duplicate  |  F2 rename")
        self._load_initial_tree()

    def set_dirty(self, state: bool = True):
        self.is_dirty = state; title = f"Family Tree — {self.current_file or 'Untitled'}"
        if self.is_dirty: title += " •"
        self.setWindowTitle(title)

    def _build_actions(self):
        self.a_undo = QAction("↩️ Undo", self); self.a_undo.setShortcut("Ctrl+Z"); self.a_undo.triggered.connect(self.undo_stack.undo)
        self.a_redo = QAction("↪️ Redo", self); self.a_redo.setShortcut("Ctrl+Shift+Z"); self.a_redo.triggered.connect(self.undo_stack.redo)
        self.a_add = QAction("➕ Add Person", self); self.a_add.setShortcut("Ctrl+N"); self.a_add.triggered.connect(self.add_person)
        self.a_pc = QAction("🔗 Connect Parent-Child", self); self.a_pc.triggered.connect(self.add_parent_child)
        self.a_sp = QAction("💍 Connect Spouses", self); self.a_sp.triggered.connect(self.add_spouse)
        self.a_path = QAction("🛤️ Find Relationship Path", self); self.a_path.setShortcut("Ctrl+P"); self.a_path.triggered.connect(self.show_path_finder)
        self.a_layout = QAction("🔄 Auto Layout", self); self.a_layout.setShortcut("Ctrl+L"); self.a_layout.triggered.connect(self.do_layout)
        self.a_del = QAction("🗑️ Delete", self); self.a_del.setShortcut("Delete"); self.a_del.triggered.connect(self.delete_selected)
        self.a_save = QAction("💾 Save", self); self.a_save.setShortcut("Ctrl+S"); self.a_save.triggered.connect(self.save)
        self.a_saveas = QAction("Save As...", self); self.a_saveas.triggered.connect(self.save_as)
        self.a_open = QAction("📂 Open", self); self.a_open.setShortcut("Ctrl+O"); self.a_open.triggered.connect(self.open)
        self.a_new = QAction("📄 New", self); self.a_new.triggered.connect(self.new_tree)
        self.a_export = QAction("🖼️ Export Tree PNG", self); self.a_export.triggered.connect(self.export_img)
        self.a_stats = QAction("📊 Statistics", self); self.a_stats.triggered.connect(self.show_stats)
        self.a_zin = QAction("🔍+ Zoom In", self); self.a_zin.setShortcut("Ctrl+="); self.a_zin.triggered.connect(lambda: self.view.scale(1.25, 1.25))
        self.a_zout = QAction("🔍− Zoom Out", self); self.a_zout.setShortcut("Ctrl+-"); self.a_zout.triggered.connect(lambda: self.view.scale(0.8, 0.8))
        self.a_fit = QAction("📐 Fit View", self); self.a_fit.setShortcut("Ctrl+0"); self.a_fit.triggered.connect(self.fit_view)
        self.a_dup = QAction("📋 Duplicate Person", self); self.a_dup.setShortcut("Ctrl+D"); self.a_dup.triggered.connect(self._dup_selected)
        self.a_rem_rel = QAction("✂️ Remove Relationship…", self); self.a_rem_rel.triggered.connect(self._rem_rel_selected)
        self.a_disc = QAction("🔗 Disconnect Person", self); self.a_disc.triggered.connect(self._disc_selected)
        self.a_rename = QAction("✏️ Rename (F2)", self); self.a_rename.setShortcut("F2"); self.a_rename.triggered.connect(self._rename_selected)
        self.a_mcts = QAction("🧠 MCTS Optimize Layout", self); self.a_mcts.setShortcut("Ctrl+M"); self.a_mcts.triggered.connect(self.mcts_optimize_layout)
        self.a_ai_insights = QAction("🔍 AI Analyze Tree", self); self.a_ai_insights.setShortcut("Ctrl+Shift+A"); self.a_ai_insights.triggered.connect(self.show_ai_insights)
        self.a_ai_predict = QAction("💡 AI Predict Relationships", self); self.a_ai_predict.triggered.connect(self.show_ai_predictions)

    def _build_toolbar(self):
        tb = QToolBar("Main"); tb.setMovable(False); self.addToolBar(tb)
        for a in (self.a_new, self.a_open, self.a_save, None, self.a_undo, self.a_redo, None, self.a_add, self.a_pc, self.a_sp, self.a_path, None, self.a_layout, self.a_mcts, self.a_fit, self.a_zin, self.a_zout, None, self.a_stats, self.a_ai_insights, self.a_export, self.a_del):
            if a is None: tb.addSeparator()
            else: tb.addAction(a)

    def _build_menus(self):
        mb = self.menuBar()
        fm = mb.addMenu("&File"); fm.addAction(self.a_new); fm.addAction(self.a_open); fm.addAction(self.a_save); fm.addAction(self.a_saveas); fm.addAction(self.a_export); fm.addSeparator(); fm.addAction(QAction("Exit", self, shortcut="Ctrl+Q", triggered=self.close))
        em = mb.addMenu("&Edit"); em.addAction(self.a_undo); em.addAction(self.a_redo); em.addSeparator(); em.addAction(self.a_add); em.addAction(self.a_dup); em.addAction(self.a_rename); em.addSeparator(); em.addAction(self.a_pc); em.addAction(self.a_sp); em.addAction(self.a_rem_rel); em.addAction(self.a_disc); em.addSeparator(); em.addAction(self.a_del)
        tm = mb.addMenu("&Tools"); tm.addAction(self.a_path); tm.addAction(self.a_stats); tm.addSeparator(); tm.addAction(self.a_mcts); tm.addAction(self.a_ai_insights); tm.addAction(self.a_ai_predict)
        vm = mb.addMenu("&View"); vm.addAction(self.a_layout); vm.addAction(self.a_fit); vm.addSeparator(); vm.addAction(self.a_zin); vm.addAction(self.a_zout)

        examples_dir = os.path.join(os.getcwd(), "example_trees")
        if os.path.exists(examples_dir):
            ex_menu = mb.addMenu("&Examples")
            for fname in sorted(os.listdir(examples_dir)):
                if fname.endswith(".json"):
                    pretty_name = fname.replace(".json", "").replace("_", " ")
                    act = ex_menu.addAction(pretty_name); act.setData(os.path.join(examples_dir, fname)); act.triggered.connect(self._open_example)

        hm = mb.addMenu("&Help"); hm.addAction(QAction("About", self, triggered=self._about))

    def _open_example(self):
        act = self.sender()
        if act and act.data():
            if not self._check_unsaved(): return
            self._open_file(act.data())

    def _refresh(self):
        self.scene.rebuild(); self.scene.auto_layout(); self.members.refresh(); self.ai_panel.refresh(); self.set_dirty(True)

    def _refresh_no_dirty(self):
        self.scene.rebuild(); self.scene.auto_layout(); self.members.refresh(); self.ai_panel.refresh()

    # ── Undo-aware mutation methods ────────────────────────────────────────
    def add_person(self):
        dlg = PersonDialog(parent=self)
        if dlg.exec() == QDialog.Accepted:
            p = dlg.get_person()
            if not p.name: return
            cmd = AddPersonCommand(self.model, p); self.undo_stack.push(cmd); self._refresh()

    def edit_person(self, pid: str):
        if pid not in self.model.persons: return
        p = self.model.persons[pid]; old_data = Person(p.name, p.gender, p.birth_date, p.death_date, p.notes, p.id)
        dlg = PersonDialog(person=p, parent=self)
        if dlg.exec() == QDialog.Accepted:
            u = dlg.get_person()
            if not u.name: return
            new_data = Person(u.name, u.gender, u.birth_date, u.death_date, u.notes, p.id)
            cmd = EditPersonCommand(self.model, pid, old_data, new_data); self.undo_stack.push(cmd); self._refresh(); self.props.show_person(pid)

    def delete_person(self, pid: str):
        if pid not in self.model.persons: return
        p = self.model.persons[pid]
        if QMessageBox.question(self, "Delete", f"Delete '{p.name}' and all their relationships?", QMessageBox.Yes | QMessageBox.No) == QMessageBox.Yes:
            cmd = RemovePersonCommand(self.model, pid); self.undo_stack.push(cmd); self._refresh(); self.props.show_person("")

    def delete_selected(self):
        sel = [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]
        if not sel: return
        if QMessageBox.question(self, "Delete", f"Delete {len(sel)} person(s)?", QMessageBox.Yes | QMessageBox.No) == QMessageBox.Yes:
            for n in sel:
                cmd = RemovePersonCommand(self.model, n.person.id); self.undo_stack.push(cmd)
            self._refresh(); self.props.show_person("")

    def add_parent_child(self):
        if len(self.model.persons) < 2: return
        preselect = ""
        if sel := [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]: preselect = sel[0].person.id
        dlg = RelationshipDialog(self.model, "parent_child", preselect_id=preselect, parent=self)
        if dlg.exec() == QDialog.Accepted:
            a, b = dlg.get_ids()
            if a == b: return
            if self.model._is_ancestor(b, a):
                QMessageBox.warning(self, "Cycle Detected", "This relationship creates a loop!"); return
            cmd = AddRelationCommand(self.model, "pc", a, b); self.undo_stack.push(cmd); self._refresh()

    def add_spouse(self):
        if len(self.model.persons) < 2: return
        preselect = ""
        if sel := [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]: preselect = sel[0].person.id
        dlg = RelationshipDialog(self.model, "spouse", preselect_id=preselect, parent=self)
        if dlg.exec() == QDialog.Accepted:
            a, b = dlg.get_ids()
            if a == b: return
            cmd = AddRelationCommand(self.model, "spouse", a, b); self.undo_stack.push(cmd); self._refresh()

    def _on_drag_relation(self, rel_type: str, id1: str, id2: str):
        """Called from scene when user drags between nodes to create a connection."""
        if rel_type == "pc":
            if self.model._is_ancestor(id2, id1):
                QMessageBox.warning(self, "Cycle Detected", "This relationship creates a loop!"); return
            cmd = AddRelationCommand(self.model, "pc", id1, id2); self.undo_stack.push(cmd); self._refresh()
        else:
            cmd = AddRelationCommand(self.model, "spouse", id1, id2); self.undo_stack.push(cmd); self._refresh()

    # ── Duplicate Person ──────────────────────────────────────────────────
    def duplicate_person(self, pid: str):
        if pid not in self.model.persons: return
        src = self.model.persons[pid]
        new_p = Person(
            name=src.name + " (copy)", gender=src.gender,
            birth_date=src.birth_date, death_date=src.death_date,
            notes=src.notes
        )
        cmd = DuplicatePersonCommand(self.model, pid, new_p)
        self.undo_stack.push(cmd)
        self._refresh()
        # Select the new node
        QTimer.singleShot(100, lambda: self._focus_member(new_p.id))

    def _dup_selected(self):
        sel = [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]
        if sel: self.duplicate_person(sel[0].person.id)

    # ── Remove Relationship ───────────────────────────────────────────────
    def remove_relationship(self, pid: str):
        if pid not in self.model.persons: return
        dlg = RemoveRelationshipDialog(self.model, pid, self)
        if dlg.exec() == QDialog.Accepted:
            result = dlg.get_removed()
            if result is None: return
            rel_type, id1, id2 = result
            if rel_type == "disconnect_all":
                cmd = DisconnectAllCommand(self.model, pid)
                self.undo_stack.push(cmd)
            else:
                cmd = RemoveRelationCommand(self.model, rel_type, id1, id2)
                self.undo_stack.push(cmd)
            self._refresh()
            self.props.show_person(pid)

    def _rem_rel_selected(self):
        sel = [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]
        if sel: self.remove_relationship(sel[0].person.id)

    # ── Disconnect Person ─────────────────────────────────────────────────
    def disconnect_person(self, pid: str):
        if pid not in self.model.persons: return
        p = self.model.persons[pid]
        has_rels = bool(self.model.get_parents(pid) or self.model.get_children(pid) or self.model.get_spouses(pid))
        if not has_rels:
            QMessageBox.information(self, "Disconnect", f"'{p.name}' has no relationships to remove."); return
        if QMessageBox.question(self, "Disconnect",
                f"Remove all relationships for '{p.name}'?\n(The person will remain in the tree.)",
                QMessageBox.Yes | QMessageBox.No) == QMessageBox.Yes:
            cmd = DisconnectAllCommand(self.model, pid)
            self.undo_stack.push(cmd)
            self._refresh()
            self.props.show_person(pid)

    def _disc_selected(self):
        sel = [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]
        if sel: self.disconnect_person(sel[0].person.id)

    # ── Select Connected ──────────────────────────────────────────────────
    def select_connected(self, pid: str, mode: str):
        if pid not in self.scene.nodes: return
        self.scene.nodes[pid].setSelected(True)
        if mode == "children":
            for cid in self.model.get_children(pid):
                if cid in self.scene.nodes: self.scene.nodes[cid].setSelected(True)
        elif mode == "spouses":
            for sid in self.model.get_spouses(pid):
                if sid in self.scene.nodes: self.scene.nodes[sid].setSelected(True)
        elif mode == "all":
            for cid in self.model.get_children(pid):
                if cid in self.scene.nodes: self.scene.nodes[cid].setSelected(True)
            for prid in self.model.get_parents(pid):
                if prid in self.scene.nodes: self.scene.nodes[prid].setSelected(True)
            for sid in self.model.get_spouses(pid):
                if sid in self.scene.nodes: self.scene.nodes[sid].setSelected(True)

    # ── Copy / Paste Person ───────────────────────────────────────────────
    def copy_person(self, pid: str):
        if pid in self.model.persons:
            src = self.model.persons[pid]
            self._clipboard_person = Person(
                name=src.name, gender=src.gender,
                birth_date=src.birth_date, death_date=src.death_date,
                notes=src.notes
            )
            self.statusBar().showMessage(f"Copied '{src.name}' — press Ctrl+V to paste", 3000)

    def paste_person(self):
        if self._clipboard_person is None:
            self.statusBar().showMessage("Nothing to paste — select a person and press Ctrl+C first", 3000)
            return
        src = self._clipboard_person
        new_p = Person(
            name=src.name + " (copy)", gender=src.gender,
            birth_date=src.birth_date, death_date=src.death_date,
            notes=src.notes
        )
        self.undo_stack.push(AddPersonCommand(self.model, new_p))
        self._refresh()
        QTimer.singleShot(100, lambda: self._focus_member(new_p.id))
        self.statusBar().showMessage(f"Pasted '{new_p.name}'", 3000)

    # ── Inline Rename (F2) ────────────────────────────────────────────────
    def rename_person(self, pid: str):
        if pid not in self.model.persons: return
        p = self.model.persons[pid]

        # Simple inline input dialog
        dlg = QDialog(self)
        dlg.setWindowTitle("Rename Person")
        dlg.setMinimumWidth(320)
        lay = QVBoxLayout(dlg)
        lbl = QLabel(f"New name for <b>{p.name}</b>:")
        lay.addWidget(lbl)
        inp = QLineEdit(p.name)
        inp.selectAll()
        inp.setFocus()
        lay.addWidget(inp)
        btns = QHBoxLayout()
        ok_btn = QPushButton("Rename"); ok_btn.setObjectName("accentBtn")
        ok_btn.clicked.connect(dlg.accept)
        cancel_btn = QPushButton("Cancel"); cancel_btn.clicked.connect(dlg.reject)
        ok_btn.setDefault(True)
        btns.addStretch(); btns.addWidget(cancel_btn); btns.addWidget(ok_btn)
        lay.addLayout(btns)
        inp.returnPressed.connect(dlg.accept)
        if dlg.exec() != QDialog.Accepted: return
        new_name = inp.text().strip()
        if not new_name or new_name == p.name: return

        old_p = Person(p.name, p.gender, p.birth_date, p.death_date, p.notes, p.id)
        new_p = Person(new_name, p.gender, p.birth_date, p.death_date, p.notes, p.id)
        cmd = EditPersonCommand(self.model, pid, old_p, new_p)
        self.undo_stack.push(cmd)
        self._refresh()
        self.props.show_person(pid)

    def _rename_selected(self):
        sel = [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]
        if sel: self.rename_person(sel[0].person.id)

    # ── Path Finder ───────────────────────────────────────────────────────
    def show_path_finder(self):
        if len(self.model.persons) < 2:
            QMessageBox.information(self, "Path Finder", "Need at least 2 people to find a path."); return
        dlg = PathFinderDialog(self.model, self)
        if dlg.exec() == QDialog.Accepted:
            start_id, end_id = dlg.get_ids()
            path = _find_path(self.model, start_id, end_id)
            if path is None:
                QMessageBox.information(self, "Path Finder", "No relationship path found between these two people.")
            else:
                names = [self.model.persons[pid].name for pid in path if pid in self.model.persons]
                # Highlight the path nodes
                self.scene.clearSelection()
                for pid in path:
                    if pid in self.scene.nodes:
                        n = self.scene.nodes[pid]; n.setSelected(True)
                        self.view.ensureVisible(n)
                # Show in properties
                rel_labels = []
                for i in range(len(path) - 1):
                    a, b = path[i], path[i + 1]
                    if b in self.model.get_children(a):
                        rel = "parent of"
                    elif a in self.model.get_children(b):
                        rel = "child of"
                    elif b in self.model.get_spouses(a):
                        rel = "spouse of"
                    else:
                        rel = "related to"
                    rel_labels.append(f"{names[i]} ({rel}) {names[i + 1]}")
                self.statusBar().showMessage("Path: " + " → ".join(rel_labels), 10000)

    # ── Layout & View ─────────────────────────────────────────────────────
    def do_layout(self):
        self.scene.auto_layout(animate=True); QTimer.singleShot(600, self.fit_view)

    def mcts_optimize_layout(self):
        """Use MCTS to find a better child ordering and re-layout."""
        if not self.model.persons:
            QMessageBox.information(self, "MCTS", "No people in the tree to optimize."); return
        self.statusBar().showMessage("MCTS: Optimizing layout...", 5000)
        QApplication.processEvents()

        optimizer = MCTSOptimizer(self.model, iterations=2000, time_limit=3.0)

        def progress(i, total):
            if i % 200 == 0:
                self.statusBar().showMessage(f"MCTS: Searching... {i}/{total} iterations", 0)

        result = optimizer.optimize(progress_callback=progress)

        if result is None:
            self.statusBar().showMessage("MCTS: Current layout is already optimal (or no optimizable families found).", 5000)
            return

        MCTSOptimizer.apply_orders(self.model, result)
        self._refresh()
        QTimer.singleShot(600, self.fit_view)
        self.statusBar().showMessage("MCTS: Layout optimized successfully!", 5000)

    # ── AI Analysis ──────────────────────────────────────────────────────
    def show_ai_insights(self):
        if not self.model.persons:
            QMessageBox.information(self, "AI Analysis", "No people in the tree to analyze."); return
        dlg = AIInsightsDialog(self.model, self)
        dlg.exec()
        # If any fixes were applied, refresh
        self._refresh()

    def show_ai_predictions(self):
        if len(self.model.persons) < 3:
            QMessageBox.information(self, "AI Predictions", "Need at least 3 people for meaningful predictions."); return

        predictor = AIRelationshipPredictor(self.model)
        insights = predictor.predict()

        # Combine with insights engine suggestions
        engine = AIInsightsEngine(self.model)
        all_insights = insights + [i for i in engine.analyze() if i.severity == "suggestion"]

        if not all_insights:
            QMessageBox.information(self, "AI Predictions", "No relationship predictions found. Your tree looks well-connected!")
            return

        # Show in a simple dialog
        dlg = QDialog(self)
        dlg.setWindowTitle("AI Relationship Predictions")
        dlg.setMinimumSize(550, 400)
        lay = QVBoxLayout(dlg)

        header = QLabel("AI Relationship Predictions")
        header.setFont(QFont("Segoe UI", 14, QFont.Bold))
        lay.addWidget(header)

        info = QLabel(f"Found <b>{len(all_insights)}</b> potential relationship(s) based on surname patterns, generation proximity, and tree structure.")
        info.setWordWrap(True)
        info.setStyleSheet("color: #6B7280; margin-bottom: 8px;")
        lay.addWidget(info)

        list_w = QTreeWidget()
        list_w.setHeaderLabels(["", "Prediction", "Details"])
        list_w.setRootIsDecorated(False)
        list_w.setAlternatingRowColors(True)
        list_w.setColumnWidth(0, 30)
        lay.addWidget(list_w)

        sev_icons = {"error": "!!", "warning": "!?", "suggestion": ">>", "info": "ii"}
        sev_colors = {"error": "#DC2626", "warning": "#D97706", "suggestion": "#10B981", "info": "#3B82F6"}

        actionable = []
        for ins in all_insights:
            icon = sev_icons.get(ins.severity, "??")
            color = sev_colors.get(ins.severity, "#6B7280")
            item = QTreeWidgetItem([icon, ins.title, ins.description])
            item.setForeground(0, QBrush(QColor(color)))
            item.setForeground(1, QBrush(QColor(color)))
            item.setToolTip(2, ins.description)
            list_w.addTopLevelItem(item)

            if ins.fix_type and ins.fix_data:
                actionable.append(ins)

            # Click to focus
            if ins.person_ids and len(ins.person_ids) >= 2:
                pid = ins.person_ids[0]
                # Store data for click handling
                item.setData(0, Qt.UserRole, ins.person_ids)

        list_w.resizeColumnToContents(0)
        list_w.resizeColumnToContents(1)

        def on_item_clicked(item, _col):
            pids = item.data(0, Qt.UserRole)
            if pids:
                self._focus_member(pids[0])

        list_w.itemClicked.connect(on_item_clicked)

        btns = QHBoxLayout()
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(dlg.reject)

        apply_all_btn = QPushButton("Apply All Spouse Suggestions")
        apply_all_btn.setObjectName("accentBtn")
        apply_all_btn.setEnabled(bool(actionable))
        def apply_all():
            count = 0
            for ins in actionable:
                if ins.fix_type == "add_spouse":
                    id1, id2 = ins.fix_data["id1"], ins.fix_data["id2"]
                    pair = tuple(sorted([id1, id2]))
                    if pair not in self.model.spouses:
                        self.model.add_spouse(id1, id2)
                        count += 1
            if count:
                self._refresh()
                dlg.accept()
                self.statusBar().showMessage(f"AI: Applied {count} spouse suggestion(s)", 5000)
            else:
                self.statusBar().showMessage("AI: All suggestions already applied", 3000)
        apply_all_btn.clicked.connect(apply_all)

        btns.addStretch()
        btns.addWidget(apply_all_btn)
        btns.addWidget(close_btn)
        lay.addLayout(btns)

        dlg.exec()

    def fit_view(self):
        r = self.scene.itemsBoundingRect().adjusted(-80, -80, 80, 80); self.view.fitInView(r, Qt.KeepAspectRatio)
        if self.view.transform().m11() > 2.5: self.view.resetTransform(); self.view.scale(2.5, 2.5)

    def show_stats(self):
        if not self.model.persons: QMessageBox.information(self, "Statistics", "No people in the tree to analyze."); return
        dlg = StatsDialog(self.model, self); dlg.exec()

    def _check_unsaved(self) -> bool:
        if self.is_dirty:
            res = QMessageBox.question(self, "Unsaved Changes", "Save changes before proceeding?", QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
            if res == QMessageBox.Save:
                if not self.current_file:
                    path, _ = QFileDialog.getSaveFileName(self, "Save As", "", "JSON (*.json)")
                    if not path: return False
                    self.current_file = path
                try:
                    with open(self.current_file, "w", encoding="utf-8") as f:
                        json.dump(self.model.to_dict(), f, indent=2, ensure_ascii=False)
                    self.set_dirty(False)
                except Exception as e:
                    QMessageBox.critical(self, "Error", str(e)); return False
                return True
            elif res == QMessageBox.Discard:
                return True
            else:
                return False
        return True

    def new_tree(self):
        if not self._check_unsaved(): return
        self.model.from_dict({}); self.current_file = ""; self.undo_stack.clear()
        self.scene.rebuild(); self.members.refresh(); self.props.show_person(""); self.set_dirty(False)

    def save(self):
        if not self.current_file: self.save_as(); return
        try:
            with open(self.current_file, "w", encoding="utf-8") as f:
                json.dump(self.model.to_dict(), f, indent=2, ensure_ascii=False)
            self.undo_stack.setClean(); self.set_dirty(False)
        except Exception as e: QMessageBox.critical(self, "Error", str(e))

    def save_as(self):
        path, _ = QFileDialog.getSaveFileName(self, "Save As", "", "JSON (*.json)")
        if path: self.current_file = path; self.save()

    def open(self):
        if not self._check_unsaved(): return
        path, _ = QFileDialog.getOpenFileName(self, "Open", "", "JSON (*.json)")
        if path: self._open_file(path)

    def _open_file(self, path: str):
        try:
            with open(path, "r", encoding="utf-8") as f: self.model.from_dict(json.load(f))
            self.current_file = path; self.undo_stack.clear(); self._refresh_no_dirty(); QTimer.singleShot(700, self.fit_view); self.set_dirty(False)
        except Exception as e: QMessageBox.critical(self, "Error", str(e))

    def export_img(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export Tree as PNG", "", "PNG (*.png)")
        if path:
            try:
                r = self.scene.itemsBoundingRect().adjusted(-80, -80, 80, 80)
                scale = 2.0
                w, h = int(r.width() * scale), int(r.height() * scale)
                pix = QPixmap(w, h); pix.fill(C["bg"])
                pa = QPainter(pix); pa.setRenderHint(QPainter.Antialiasing); pa.setRenderHint(QPainter.TextAntialiasing)
                pa.scale(scale, scale); self.scene.render(pa, QRectF(pix.rect()), r); pa.end(); pix.save(path)
                self.statusBar().showMessage(f"Tree exported successfully to {path}", 5000)
            except Exception as e: QMessageBox.critical(self, "Error", str(e))

    def _focus_member(self, pid: str):
        if pid in self.scene.nodes:
            n = self.scene.nodes[pid]; self.scene.clearSelection(); n.setSelected(True); self.view.ensureVisible(n)

    def _about(self):
        QMessageBox.about(self, "About",
            "<h3>Family Tree Creator</h3>"
            "<p>Enhanced Visualization & Charts Edition</p>"
            "<p><b>Features:</b> Undo/Redo, Drag-to-Connect, Path Finder, Age Stats, Charts,<br>"
            "Duplicate, Remove Relationship, Disconnect, Select Connected, Copy/Paste, Rename (F2),<br>"
            "MCTS Layout Optimization, AI Tree Analysis, AI Relationship Predictor</p>"
            "<p><b>Shortcuts:</b> Ctrl+Z/Y Undo/Redo | Ctrl+D Duplicate | F2 Rename<br>"
            "Ctrl+M MCTS Optimize | Ctrl+Shift+A AI Analyze | Ctrl+P Find Path | Ctrl+L Layout</p>")

    def closeEvent(self, event):
        if not self._check_unsaved(): event.ignore(); return
        super().closeEvent(event)

    def _load_initial_tree(self):
        if os.path.exists(SAMPLE_FILE): self._open_file(SAMPLE_FILE)
        else: self._generate_sample_data()
        QTimer.singleShot(700, self.fit_view)

    def _generate_sample_data(self):
        m = self.model
        gp  = Person("Robert Smith",   "Male",   "1935", "2010", "Patriarch")
        gm  = Person("Margaret Smith", "Female", "1938", "2015", "Matriarch")
        dad = Person("James Smith",    "Male",   "1960", "",     "Eldest son")
        mom = Person("Linda Smith",    "Female", "1962", "",     "née Johnson")
        unc = Person("Thomas Smith",   "Male",   "1963", "",     "Younger son")
        ant = Person("Patricia Smith", "Female", "1965", "",     "née Williams")
        c1  = Person("Emily Smith",    "Female", "1988", "")
        c2  = Person("Michael Smith",  "Male",   "1991", "")
        c3  = Person("Sarah Smith",    "Female", "1990", "")
        c4  = Person("David Smith",    "Male",   "1993", "")

        for p in [gp, gm, dad, mom, unc, ant, c1, c2, c3, c4]: m.add_person(p)

        m.add_parent_child(gp.id, dad.id); m.add_parent_child(gm.id, dad.id)
        m.add_parent_child(gp.id, unc.id); m.add_parent_child(gm.id, unc.id)
        m.add_spouse(gp.id, gm.id); m.add_spouse(dad.id, mom.id); m.add_spouse(unc.id, ant.id)
        m.add_parent_child(dad.id, c1.id); m.add_parent_child(mom.id, c1.id)
        m.add_parent_child(dad.id, c2.id); m.add_parent_child(mom.id, c2.id)
        m.add_parent_child(unc.id, c3.id); m.add_parent_child(ant.id, c3.id)
        m.add_parent_child(unc.id, c4.id); m.add_parent_child(ant.id, c4.id)

        try:
            with open(SAMPLE_FILE, "w", encoding="utf-8") as f: json.dump(m.to_dict(), f, indent=2, ensure_ascii=False)
        except Exception: pass

        self.current_file = SAMPLE_FILE; self._refresh_no_dirty(); self.fit_view(); self.set_dirty(False)


# ─── Entry Point ──────────────────────────────────────────────────────────────
def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")

    palette = app.palette()
    palette.setColor(QPalette.Window, QColor("#FAFAFA")); palette.setColor(QPalette.WindowText, QColor("#2C2C2C"))
    palette.setColor(QPalette.Base, QColor("#FFFFFF")); palette.setColor(QPalette.AlternateBase, QColor("#F5F5F5"))
    palette.setColor(QPalette.ToolTipBase, QColor("#FFFFFF")); palette.setColor(QPalette.ToolTipText, QColor("#2C2C2C"))
    palette.setColor(QPalette.Text, QColor("#2C2C2C")); palette.setColor(QPalette.Button, QColor("#EEEEEE"))
    palette.setColor(QPalette.ButtonText, QColor("#2C2C2C")); palette.setColor(QPalette.BrightText, QColor("#FF4081"))
    palette.setColor(QPalette.Link, QColor("#42A5F5")); palette.setColor(QPalette.Highlight, QColor("#42A5F5"))
    palette.setColor(QPalette.HighlightedText, QColor("#FFFFFF"))
    app.setPalette(palette)

    app.setStyleSheet("""
        QToolBar { spacing: 6px; padding: 6px; border: none; background: #FFFFFF; border-bottom: 1px solid #E0E0E0; }
        QToolBar QToolButton { border: 1px solid #E0E0E0; border-radius: 4px; padding: 5px 10px; background: #FFFFFF; color: #2C2C2C; }
        QToolBar QToolButton:hover { background: #F5F5F5; border-color: #BDBDBD; }
        QToolBar QToolButton:pressed { background: #E0E0E0; }
        QDockWidget { border: none; font-weight: medium; }
        QDockWidget::title { text-align: left; background: #FFFFFF; padding: 8px; border-bottom: 1px solid #E0E0E0; }
        QTreeWidget { border: none; background: #FFFFFF; border-right: 1px solid #E0E0E0; }
        QGroupBox { font-weight: medium; border: 1px solid #E0E0E0; border-radius: 4px; margin-top: 12px; padding-top: 16px; }
        QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 5px; }
        QPushButton#accentBtn { background: #3B82F6; color: #FFFFFF; border: none; border-radius: 4px; padding: 8px 16px; font-weight: bold; }
        QPushButton#accentBtn:hover { background: #2563EB; }
        QStatusBar { background: #FFFFFF; color: #9E9E9E; border-top: 1px solid #E0E0E0; }
        QMenuBar { background: #FFFFFF; border-bottom: 1px solid #E0E0E0; }
        QMenuBar::item:selected { background: #E0E0E0; }
        QMenu { background: #FFFFFF; border: 1px solid #E0E0E0; }
        QMenu::item:selected { background: #3B82F6; color: #FFFFFF; }
        QTabWidget::pane { border: 1px solid #E0E0E0; background: #FFFFFF; }
        QTabBar::tab { background: #F5F5F5; padding: 8px 20px; border: 1px solid #E0E0E0; border-bottom: none; border-top-left-radius: 4px; border-top-right-radius: 4px; }
        QTabBar::tab:selected { background: #FFFFFF; }
    """)

    window = MainWindow()
    window.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()