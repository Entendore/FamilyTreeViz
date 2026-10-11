#!/usr/bin/env python3
"""
Family Tree Creator — Enhanced Visualization & Charts Edition
A PySide6 application for creating and visualizing family trees.
"""

import sys
import os
import json
import uuid
from collections import deque

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QGraphicsScene, QGraphicsView,
    QGraphicsItem, QGraphicsPathItem, QDialog, QVBoxLayout,
    QHBoxLayout, QFormLayout, QLabel, QLineEdit, QComboBox,
    QTextEdit, QPushButton, QToolBar, QFileDialog, QMessageBox,
    QDockWidget, QTreeWidget, QTreeWidgetItem, QMenu, QWidget,
    QGroupBox, QSizePolicy, QTabWidget,
)
from PySide6.QtCore import Qt, QPointF, QRectF, Signal, QTimer
from PySide6.QtGui import (
    QPainter, QPen, QBrush, QColor, QFont, QLinearGradient,
    QPainterPath, QAction, QPixmap, QPalette, QTransform,
)

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
        for pd in data.get("persons", {}).values():
            p = Person.from_dict(pd); self.persons[p.id] = p
        self.parent_child = [tuple(x) for x in data.get("parent_child", [])]
        self.spouses = [tuple(x) for x in data.get("spouses", [])]


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

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemPositionHasChanged:
            sc = self.scene()
            if sc and hasattr(sc, 'update_connectors') and not getattr(sc, '_animating', False): sc.update_connectors()
        return super().itemChange(change)

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
        if not self.child_nodes or not self.parent_nodes: self.setPath(path); return
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


# ─── Scene ────────────────────────────────────────────────────────────────────
class FamilyTreeScene(QGraphicsScene):
    edit_person_requested = Signal(str); delete_person_requested = Signal(str); selection_changed_sig = Signal(str)

    def __init__(self, model: FamilyTreeModel):
        super().__init__()
        self.model = model; self.nodes: dict[str, PersonNode] = {}; self.brackets: list[FamilyBracket] = []
        self.spouse_links: list[SpouseLink] = []; self.gen_levels: dict[str, int] = {}
        self._animating = False; self._anim_timer = QTimer(); self._anim_timer.setInterval(16); self._anim_timer.timeout.connect(self._anim_step)
        self._anim_start: dict[str, QPointF] = {}; self._anim_target: dict[str, QPointF] = {}; self._anim_progress = 0.0
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
        left, top = int(rect.left()) - int(rect.left()) % gs, int(rect.top()) - int(rect.top()) % gs; pts = []
        x = left
        while x < rect.right(): y = top; while y < rect.bottom(): pts.append(QPointF(x, y)); y += gs; x += gs
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
        for pid in self._anim_start: s, e = self._anim_start[pid], self._anim_target[pid]; self.nodes[pid].setPos(s + (e - s) * t)
        self.update_connectors()

    def _compute_gen_levels(self):
        gens: dict[str, int] = {}; roots = self.model.get_roots(); q: deque[str] = deque()
        for r in roots: gens[r] = 0; q.append(r)
        while q:
            cur = q.popleft(); g = gens[cur]
            for c in self.model.get_children(cur): ng = g + 1; gens[c] = ng if c not in gens else max(gens[c], ng); q.append(c)
            for s in self.model.get_spouses(cur):
                if s not in gens: gens[s] = g; q.append(s)
        self.gen_levels = gens

    def _compute_layout(self) -> dict[str, QPointF]:
        if not self.model.persons: return {}
        gens: dict[str, int] = {}; roots = self.model.get_roots(); q: deque[str] = deque()
        for r in roots: gens[r] = 0; q.append(r)
        while q:
            cur = q.popleft(); g = gens[cur]
            for c in self.model.get_children(cur): ng = g + 1; gens[c] = ng if c not in gens else max(gens[c], ng); q.append(c)
            for s in self.model.get_spouses(cur):
                if s not in gens: gens[s] = g; q.append(s)
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

    def contextMenuEvent(self, ev):
        item = self.itemAt(ev.scenePos(), QTransform()); menu = QMenu()
        if isinstance(item, PersonNode):
            pid = item.person.id; a_edit = menu.addAction("✏️  Edit"); a_del = menu.addAction("🗑️  Delete"); menu.addSeparator()
            a_child = menu.addAction("👶  Add Child"); a_spouse = menu.addAction("💍  Add Spouse"); a_parent = menu.addAction("⬆️  Add Parent")
            act = menu.exec(ev.screenPos())
            if act == a_edit: self.edit_person_requested.emit(pid)
            elif act == a_del: self.delete_person_requested.emit(pid)
            elif act == a_child: self._quick_add_child(pid)
            elif act == a_spouse: self._quick_add_spouse(pid)
            elif act == a_parent: self._quick_add_parent(pid)
        else:
            a_add = menu.addAction("➕  Add Person"); a_lay = menu.addAction("🔄  Auto Layout")
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
        if ev.key() == Qt.Key_Delete: self.delete_requested.emit()
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
        self.setMinimumSize(850, 650)
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
        while q:
            cur = q.popleft(); g = gens[cur]
            for c in self.model.get_children(cur):
                if c not in gens or gens[c] < g + 1: gens[c] = g + 1; q.append(c)
            for s in self.model.get_spouses(cur):
                if s not in gens: gens[s] = g; q.append(s)
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
        lay.addWidget(info)
        lay.addStretch()
        return w

    def _create_charts_tab(self) -> QWidget:
        w = QWidget(); lay = QHBoxLayout(w)
        
        self.fig = Figure(figsize=(10, 5), facecolor=MC["bg"])
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

        # Chart 1: Gender Distribution
        ax1 = self.fig.add_subplot(121)
        labels, sizes, colors = [], [], []
        if males: labels.append("Male"); sizes.append(males); colors.append(MC["male"])
        if females: labels.append("Female"); sizes.append(females); colors.append(MC["female"])
        if others: labels.append("Other"); sizes.append(others); colors.append(MC["other"])
        ax1.pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%', startangle=90, textprops={'color': MC["text"]})
        ax1.set_title("Gender Distribution", color=MC["text"], pad=20)

        # Chart 2: Members per Generation
        ax2 = self.fig.add_subplot(122)
        gens = self._get_generations()
        if gens:
            gen_counts = {}
            for g in gens.values(): gen_counts[g] = gen_counts.get(g, 0) + 1
            x = [f"Gen {g+1}" for g in sorted(gen_counts.keys())]
            y = [gen_counts[g] for g in sorted(gen_counts.keys())]
            bars = ax2.bar(x, y, color=MC["male"], width=0.6)
            ax2.set_title("Members per Generation", color=MC["text"], pad=20)
            ax2.tick_params(colors=MC["text"])
            ax2.spines['top'].set_visible(False)
            ax2.spines['right'].set_visible(False)
            ax2.spines['bottom'].set_color(MC["grid"])
            ax2.spines['left'].set_color(MC["grid"])
            for bar in bars:
                ax2.text(bar.get_x() + bar.get_width()/2., bar.get_height(), f'{int(bar.get_height())', ha='center', va='bottom', color=MC["text"])

        self.fig.tight_layout(pad=3.0)
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


# ─── Panels ───────────────────────────────────────────────────────────────────
class PropertiesPanel(QWidget):
    edit_requested = Signal(str); delete_requested = Signal(str)
    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent); self.model = model; self._pid: str | None = None
        lay = QVBoxLayout(self); lay.setContentsMargins(12, 12, 12, 12)
        self.title = QLabel("Details"); self.title.setFont(QFont("Segoe UI", 13, QFont.Medium)); self.title.setStyleSheet("color: #1F2937;"); lay.addWidget(self.title)
        g = QGroupBox("Information"); gl = QFormLayout(g)
        self.l_name = QLabel("-"); self.l_gender = QLabel("-"); self.l_birth = QLabel("-"); self.l_death = QLabel("-"); self.l_notes = QLabel("-"); self.l_notes.setWordWrap(True)
        gl.addRow("Name:", self.l_name); gl.addRow("Gender:", self.l_gender); gl.addRow("Birth:", self.l_birth); gl.addRow("Death:", self.l_death); gl.addRow("Notes:", self.l_notes); lay.addWidget(g)
        rg = QGroupBox("Relationships"); rl = QVBoxLayout(rg); self.l_rel = QLabel("No selection"); self.l_rel.setWordWrap(True); rl.addWidget(self.l_rel); lay.addWidget(rg)
        btns = QHBoxLayout(); self.b_edit = QPushButton("Edit"); self.b_del = QPushButton("Delete"); self.b_edit.setEnabled(False); self.b_del.setEnabled(False)
        self.b_edit.clicked.connect(lambda: self.edit_requested.emit(self._pid or "")); self.b_del.clicked.connect(lambda: self.delete_requested.emit(self._pid or ""))
        btns.addWidget(self.b_edit); btns.addWidget(self.b_del); lay.addLayout(btns); lay.addStretch()

    def show_person(self, pid: str):
        self._pid = pid or None
        if not pid or pid not in self.model.persons:
            self.title.setText("Details"); [w.setText("-") for w in (self.l_name, self.l_gender, self.l_birth, self.l_death, self.l_notes)]; self.l_rel.setText("No selection"); self.b_edit.setEnabled(False); self.b_del.setEnabled(False); return
        p = self.model.persons[pid]; self.title.setText(p.name); self.l_name.setText(p.name); self.l_gender.setText(p.gender); self.l_birth.setText(p.birth_date or "Unknown"); self.l_death.setText(p.death_date or "Alive"); self.l_notes.setText(p.notes or "None")
        lines = []
        if par := self.model.get_parents(pid): lines.append("Parents: " + ", ".join(self.model.persons[x].name for x in par if x in self.model.persons))
        if ch := self.model.get_children(pid): lines.append("Children: " + ", ".join(self.model.persons[x].name for x in ch if x in self.model.persons))
        if sp := self.model.get_spouses(pid): lines.append("Spouse(s): " + ", ".join(self.model.persons[x].name for x in sp if x in self.model.persons))
        self.l_rel.setText("\n".join(lines) if lines else "No relationships"); self.b_edit.setEnabled(True); self.b_del.setEnabled(True)


class MembersPanel(QWidget):
    member_selected = Signal(str)
    def __init__(self, model: FamilyTreeModel, parent=None):
        super().__init__(parent); self.model = model
        lay = QVBoxLayout(self); lay.setContentsMargins(4, 4, 4, 4); header = QLabel("Members"); header.setFont(QFont("Segoe UI", 10, QFont.Medium)); lay.addWidget(header)
        self.tree = QTreeWidget(); self.tree.setHeaderLabels(["Name", "Born"]); self.tree.setAlternatingRowColors(True); self.tree.setRootIsDecorated(False); self.tree.itemClicked.connect(self._clicked); lay.addWidget(self.tree)

    def _clicked(self, item, _):
        if pid := item.data(0, Qt.UserRole): self.member_selected.emit(pid)

    def refresh(self):
        self.tree.clear()
        for pid, p in sorted(self.model.persons.items(), key=lambda x: x[1].name):
            it = QTreeWidgetItem([p.name, p.birth_date]); it.setData(0, Qt.UserRole, pid)
            if p.gender == "Male": it.setForeground(0, QBrush(C["male"]))
            elif p.gender == "Female": it.setForeground(0, QBrush(C["female"]))
            else: it.setForeground(0, QBrush(C["other"]))
            self.tree.addTopLevelItem(it)
        for i in range(2): self.tree.resizeColumnToContents(i)


# ─── Main Window ──────────────────────────────────────────────────────────────
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Family Tree Creator"); self.resize(1500, 920)
        self.model = FamilyTreeModel(); self.is_dirty = False; self.current_file = ""

        self.scene = FamilyTreeScene(self.model)
        self.scene.edit_person_requested.connect(self.edit_person); self.scene.delete_person_requested.connect(self.delete_person)
        self.view = FamilyTreeView(self.scene); self.view.delete_requested.connect(self.delete_selected); self.setCentralWidget(self.view)

        self.props = PropertiesPanel(self.model); self.props.edit_requested.connect(self.edit_person); self.props.delete_requested.connect(self.delete_person)
        self.scene.selection_changed_sig.connect(self.props.show_person)
        self.members = MembersPanel(self.model); self.members.member_selected.connect(self._focus_member)

        dock_r = QDockWidget("Properties", self); dock_r.setWidget(self.props); dock_r.setMinimumWidth(230); self.addDockWidget(Qt.RightDockWidgetArea, dock_r)
        dock_l = QDockWidget("Members", self); dock_l.setWidget(self.members); dock_l.setMinimumWidth(190); self.addDockWidget(Qt.LeftDockWidgetArea, dock_l)

        self._build_actions(); self._build_toolbar(); self._build_menus()
        self.statusBar().showMessage("Right-click canvas to add a person  •  Double-click node to edit")
        self._load_initial_tree()

    def set_dirty(self, state: bool = True):
        self.is_dirty = state; title = f"Family Tree — {self.current_file or 'Untitled'}"
        if self.is_dirty: title += " •"
        self.setWindowTitle(title)

    def _build_actions(self):
        self.a_add = QAction("➕ Add Person", self); self.a_add.setShortcut("Ctrl+N"); self.a_add.triggered.connect(self.add_person)
        self.a_pc = QAction("🔗 Connect Parent-Child", self); self.a_pc.triggered.connect(self.add_parent_child)
        self.a_sp = QAction("💍 Connect Spouses", self); self.a_sp.triggered.connect(self.add_spouse)
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

    def _build_toolbar(self):
        tb = QToolBar("Main"); tb.setMovable(False); self.addToolBar(tb)
        for a in (self.a_new, self.a_open, self.a_save, None, self.a_add, self.a_pc, self.a_sp, None, self.a_layout, self.a_fit, self.a_zin, self.a_zout, None, self.a_stats, self.a_export, self.a_del):
            if a is None: tb.addSeparator()
            else: tb.addAction(a)

    def _build_menus(self):
        mb = self.menuBar()
        fm = mb.addMenu("&File"); fm.addAction(self.a_new); fm.addAction(self.a_open); fm.addAction(self.a_save); fm.addAction(self.a_saveas); fm.addAction(self.a_export); fm.addSeparator(); fm.addAction(QAction("Exit", self, shortcut="Ctrl+Q", triggered=self.close))
        em = mb.addMenu("&Edit"); em.addAction(self.a_add); em.addAction(self.a_pc); em.addAction(self.a_sp); em.addSeparator(); em.addAction(self.a_del)
        vm = mb.addMenu("&View"); vm.addAction(self.a_layout); vm.addAction(self.a_fit); vm.addSeparator(); vm.addAction(self.a_zin); vm.addAction(self.a_zout)
        vm.addAction(self.a_stats) # Added Stats to View Menu

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

    def _refresh(self): self.scene.rebuild(); self.scene.auto_layout(); self.members.refresh(); self.set_dirty(True)
    def _refresh_no_dirty(self): self.scene.rebuild(); self.scene.auto_layout(); self.members.refresh()

    def add_person(self):
        dlg = PersonDialog(parent=self)
        if dlg.exec() == QDialog.Accepted:
            p = dlg.get_person()
            if not p.name: return
            self.model.add_person(p); self._refresh()

    def edit_person(self, pid: str):
        if pid not in self.model.persons: return
        p = self.model.persons[pid]; dlg = PersonDialog(person=p, parent=self)
        if dlg.exec() == QDialog.Accepted:
            u = dlg.get_person()
            if not u.name: return
            p.name, p.gender, p.birth_date, p.death_date, p.notes = u.name, u.gender, u.birth_date, u.death_date, u.notes
            self._refresh(); self.props.show_person(pid)

    def delete_person(self, pid: str):
        if pid not in self.model.persons: return
        p = self.model.persons[pid]
        if QMessageBox.question(self, "Delete", f"Delete '{p.name}'?", QMessageBox.Yes | QMessageBox.No) == QMessageBox.Yes:
            self.model.remove_person(pid); self._refresh(); self.props.show_person("")

    def delete_selected(self):
        sel = [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]
        if not sel: return
        if QMessageBox.question(self, "Delete", f"Delete {len(sel)} person(s)?", QMessageBox.Yes | QMessageBox.No) == QMessageBox.Yes:
            for n in sel: self.model.remove_person(n.person.id)
            self._refresh(); self.props.show_person("")

    def add_parent_child(self):
        if len(self.model.persons) < 2: return
        preselect = ""
        if sel := [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]: preselect = sel[0].person.id
        dlg = RelationshipDialog(self.model, "parent_child", preselect_id=preselect, parent=self)
        if dlg.exec() == QDialog.Accepted:
            a, b = dlg.get_ids()
            if a == b: return
            if not self.model.add_parent_child(a, b): QMessageBox.warning(self, "Cycle Detected", "This relationship creates a loop!"); return
            self._refresh()

    def add_spouse(self):
        if len(self.model.persons) < 2: return
        preselect = ""
        if sel := [i for i in self.scene.selectedItems() if isinstance(i, PersonNode)]: preselect = sel[0].person.id
        dlg = RelationshipDialog(self.model, "spouse", preselect_id=preselect, parent=self)
        if dlg.exec() == QDialog.Accepted:
            a, b = dlg.get_ids()
            if a == b: return
            self.model.add_spouse(a, b); self._refresh()

    def do_layout(self): self.scene.auto_layout(animate=True); QTimer.singleShot(600, self.fit_view)

    def fit_view(self):
        r = self.scene.itemsBoundingRect().adjusted(-80, -80, 80, 80); self.view.fitInView(r, Qt.KeepAspectRatio)
        if self.view.transform().m11() > 2.5: self.view.resetTransform(); self.view.scale(2.5, 2.5)

    def show_stats(self):
        if not self.model.persons: QMessageBox.information(self, "Statistics", "No people in the tree to analyze."); return
        dlg = StatsDialog(self.model, self); dlg.exec()

    def _check_unsaved(self) -> bool:
        if self.is_dirty:
            res = QMessageBox.question(self, "Unsaved Changes", "Save changes before proceeding?", QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
            if res == QMessageBox.Save: self.save(); return True
            elif res == QMessageBox.Discard: return True
            else: return False
        return True

    def new_tree(self):
        if not self._check_unsaved(): return
        self.model.from_dict({}); self.current_file = ""; self.scene.rebuild(); self.members.refresh(); self.props.show_person(""); self.set_dirty(False)

    def save(self):
        if not self.current_file: self.save_as(); return
        try:
            with open(self.current_file, "w", encoding="utf-8") as f: json.dump(self.model.to_dict(), f, indent=2, ensure_ascii=False); self.set_dirty(False)
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
            self.current_file = path; self._refresh_no_dirty(); self.fit_view(); self.set_dirty(False)
        except Exception as e: QMessageBox.critical(self, "Error", str(e))

    def export_img(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export Tree as PNG", "", "PNG (*.png)")
        if path:
            try:
                r = self.scene.itemsBoundingRect().adjusted(-80, -80, 80, 80)
                # High Resolution 2x Export for crisp text and lines
                scale = 2.0
                w, h = int(r.width() * scale), int(r.height() * scale)
                pix = QPixmap(w, h); pix.fill(C["bg"])
                pa = QPainter(pix); pa.setRenderHint(QPainter.Antialiasing); pa.setRenderHint(QPainter.TextAntialiasing)
                pa.scale(scale, scale); self.scene.render(pa, QRectF(pix.rect()), r); pa.end(); pix.save(path)
                self.statusBar().showMessage(f"Tree exported successfully to {path}", 5000)
            except Exception as e: QMessageBox.critical(self, "Error", str(e))

    def _focus_member(self, pid: str):
        if pid in self.scene.nodes: n = self.scene.nodes[pid]; self.scene.clearSelection(); n.setSelected(True); self.view.ensureVisible(n)

    def _about(self):
        QMessageBox.about(self, "About", "<h3>Family Tree Creator</h3><p>Enhanced Visualization & Charts Edition</p>")

    def closeEvent(self, event):
        if not self._check_unsaved(): event.ignore(); return
        super().closeEvent(event)

    def _load_initial_tree(self):
        if os.path.exists(SAMPLE_FILE): self._open_file(SAMPLE_FILE)
        else: self._generate_sample_data()

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