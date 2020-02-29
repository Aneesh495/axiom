/**
 * app.js
 *
 * Interactive Proof DAG and Implication Graph Visualizer for Axiom.
 * Renders resolution trees, 1-UIP conflict cuts, and Craig Interpolation barriers.
 */

const EXAMPLES = {
  php: `(set-logic QF_UF)
; PHP(4, 3) Pigeonhole Principle (Provably UNSAT)
(declare-const p11 Bool) (declare-const p12 Bool) (declare-const p13 Bool)
(declare-const p21 Bool) (declare-const p22 Bool) (declare-const p23 Bool)
(declare-const p31 Bool) (declare-const p32 Bool) (declare-const p33 Bool)
(declare-const p41 Bool) (declare-const p42 Bool) (declare-const p43 Bool)
(assert (or p11 p12 p13))
(assert (or p21 p22 p23))
(assert (or p31 p32 p33))
(assert (or p41 p42 p43))
(assert (not (and p11 p21))) (assert (not (and p11 p31))) (assert (not (and p11 p41)))
(assert (not (and p21 p31))) (assert (not (and p21 p41))) (assert (not (and p31 p41)))
(check-sat)`,

  gcd: `; Euclidean GCD Verification Condition
(declare-const a Int)
(declare-const b Int)
(assert (> a 0))
(assert (> b 0))
; Loop invariant preserved across subtraction step
(assert (not (=> (and (> a 0) (> b 0)) (> (- a b) 0))))
(check-sat)`,

  simplex: `(set-logic QF_LRA)
; 2D Polytope Satisfiability
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ x y) 10.0))
(assert (>= x 1.0))
(assert (>= y 2.0))
(assert (<= (- x y) 3.0))
(check-sat)`,

  diophantine: `(set-logic QF_LIA)
; Diophantine GCD Refutation
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 6 x) (* 9 y)) 11))
(check-sat)`,

  array: `(set-logic QF_AX)
; McCarthy ROW2 Refutation
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-const a (Array Index Elem))
(declare-const i Index)
(declare-const j Index)
(declare-const v Elem)
(assert (distinct i j))
(assert (distinct (select (store a i v) j) (select a j)))
(check-sat)`
};

// Synthetic Proof DAG Data
const MOCK_DAGS = {
  php: {
    result: "UNSAT",
    time: "0.36 ms",
    depth: 5,
    nodes: [
      { id: "C_1", label: "C1", x: 100, y: 80, lits: "p11 | p12 | p13", isConflict: false },
      { id: "C_2", label: "C2", x: 260, y: 80, lits: "p21 | p22 | p23", isConflict: false },
      { id: "C_3", label: "C3", x: 420, y: 80, lits: "~p11 | ~p21", isConflict: false },
      { id: "C_4", label: "C4", x: 580, y: 80, lits: "~p12 | ~p22", isConflict: false },
      { id: "C_5", label: "C5", x: 740, y: 80, lits: "~p13 | ~p23", isConflict: false },
      { id: "C_6", label: "Res1", x: 180, y: 200, lits: "p12 | p13 | ~p21", isConflict: false, ante: ["C_1", "C_3"], pivot: "p11" },
      { id: "C_7", label: "Res2", x: 500, y: 200, lits: "p13 | ~p21 | ~p22", isConflict: false, ante: ["C_6", "C_4"], pivot: "p12" },
      { id: "C_8", label: "1-UIP", x: 340, y: 320, lits: "~p21 | ~p22 | ~p23", isConflict: true, ante: ["C_7", "C_5"], pivot: "p13" },
      { id: "C_9", label: "EMPTY", x: 300, y: 440, lits: "[EMPTY CLAUSE]", isConflict: true, ante: ["C_2", "C_8"], pivot: "p21" }
    ],
    edges: [
      { from: "C_1", to: "C_6" },
      { from: "C_3", to: "C_6" },
      { from: "C_6", to: "C_7" },
      { from: "C_4", to: "C_7" },
      { from: "C_7", to: "C_8", isConflict: true },
      { from: "C_5", to: "C_8", isConflict: true },
      { from: "C_2", to: "C_9", isConflict: true },
      { from: "C_8", to: "C_9", isConflict: true }
    ]
  },
  gcd: {
    result: "VERIFIED",
    time: "1.18 ms",
    depth: 4,
    nodes: [
      { id: "G_1", label: "Pre", x: 200, y: 100, lits: "a > 0 /\\ b > 0", isConflict: false },
      { id: "G_2", label: "Inv", x: 400, y: 100, lits: "gcd(a, b) == gcd(x, y)", isConflict: false },
      { id: "G_3", label: "Trans", x: 300, y: 220, lits: "x' = x - y", isConflict: false, ante: ["G_1", "G_2"], pivot: "x" },
      { id: "G_4", label: "Pres", x: 300, y: 340, lits: "gcd(x - y, y) == gcd(x, y)", isConflict: false, ante: ["G_3"], pivot: "gcd_step" },
      { id: "G_5", label: "QED", x: 300, y: 460, lits: "Valid Invariant Barrier", isConflict: false, ante: ["G_4"] }
    ],
    edges: [
      { from: "G_1", to: "G_3" },
      { from: "G_2", to: "G_3" },
      { from: "G_3", to: "G_4" },
      { from: "G_4", to: "G_5" }
    ]
  }
};

class ProofVisualizer {
  constructor() {
    this.svg = document.getElementById("graph-svg");
    this.container = document.getElementById("graph-container");
    this.viewport = document.getElementById("viewport");
    this.inspector = document.getElementById("inspector-panel");

    this.panX = 0;
    this.panY = 0;
    this.zoom = 1.0;
    this.isDragging = false;
    this.dragStart = { x: 0, y: 0 };

    this.currentData = MOCK_DAGS.php;
    this.initEvents();
    this.loadExample("php");
  }

  initEvents() {
    // Zoom and Pan
    this.viewport.addEventListener("mousedown", (e) => {
      if (e.target === this.svg || e.target.tagName === "svg" || e.target.id === "graph-container") {
        this.isDragging = true;
        this.dragStart = { x: e.clientX - this.panX, y: e.clientY - this.panY };
      }
    });

    window.addEventListener("mousemove", (e) => {
      if (this.isDragging) {
        this.panX = e.clientX - this.dragStart.x;
        this.panY = e.clientY - this.dragStart.y;
        this.updateTransform();
      }
    });

    window.addEventListener("mouseup", () => {
      this.isDragging = false;
    });

    this.viewport.addEventListener("wheel", (e) => {
      e.preventDefault();
      const zoomFactor = e.deltaY < 0 ? 1.1 : 0.9;
      this.zoom *= zoomFactor;
      this.zoom = Math.max(0.2, Math.min(3.0, this.zoom));
      this.updateTransform();
    });

    // Buttons
    document.getElementById("btn-zoom-in").addEventListener("click", () => {
      this.zoom = Math.min(3.0, this.zoom * 1.2);
      this.updateTransform();
    });

    document.getElementById("btn-zoom-out").addEventListener("click", () => {
      this.zoom = Math.max(0.2, this.zoom / 1.2);
      this.updateTransform();
    });

    document.getElementById("btn-zoom-fit").addEventListener("click", () => {
      this.panX = 60;
      this.panY = 60;
      this.zoom = 1.0;
      this.updateTransform();
    });

    document.getElementById("example-select").addEventListener("change", (e) => {
      this.loadExample(e.target.value);
    });

    document.getElementById("btn-verify").addEventListener("click", () => {
      this.renderGraph(this.currentData);
    });

    document.getElementById("btn-close-inspector").addEventListener("click", () => {
      this.inspector.style.display = "none";
    });
  }

  loadExample(key) {
    const text = EXAMPLES[key] || EXAMPLES.php;
    document.getElementById("smt-input").value = text;
    this.currentData = MOCK_DAGS[key] || MOCK_DAGS.php;
    this.renderGraph(this.currentData);
  }

  updateTransform() {
    this.container.setAttribute("transform", `translate(${this.panX}, ${this.panY}) scale(${this.zoom})`);
  }

  renderGraph(data) {
    this.container.innerHTML = "";
    document.getElementById("stat-result").textContent = data.result;
    document.getElementById("stat-result").className = "stat-value " + (data.result === "UNSAT" ? "val-unsat" : "val-sat");
    document.getElementById("stat-clauses").textContent = data.nodes.length;
    document.getElementById("stat-depth").textContent = data.depth;
    document.getElementById("stat-time").textContent = data.time;
    document.getElementById("node-count-label").textContent = `Displaying ${data.nodes.length} Proof Nodes`;

    // Render Edges
    const nodeMap = new Map();
    data.nodes.forEach(n => nodeMap.set(n.id, n));

    data.edges.forEach(e => {
      const src = nodeMap.get(e.from);
      const dst = nodeMap.get(e.to);
      if (!src || !dst) return;

      const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const dx = dst.x - src.x;
      const dy = dst.y - src.y;
      const d = `M ${src.x} ${src.y} Q ${src.x + dx * 0.2} ${src.y + dy * 0.8} ${dst.x} ${dst.y}`;

      path.setAttribute("d", d);
      path.setAttribute("class", e.isConflict ? "edge-path edge-conflict" : "edge-path");
      path.setAttribute("marker-end", e.isConflict ? "url(#arrow-conflict)" : "url(#arrow)");
      this.container.appendChild(path);
    });

    // Render Nodes
    data.nodes.forEach(n => {
      const g = document.createElementNS("http://www.w3.org/2000/svg", "g");
      g.setAttribute("transform", `translate(${n.x}, ${n.y})`);

      const circle = document.createElementNS("http://www.w3.org/2000/svg", "circle");
      circle.setAttribute("r", 20);
      circle.setAttribute("class", n.isConflict ? "node-circle node-conflict" : "node-circle");

      const label = document.createElementNS("http://www.w3.org/2000/svg", "text");
      label.setAttribute("class", "node-label");
      label.textContent = n.label;

      g.appendChild(circle);
      g.appendChild(label);

      g.addEventListener("click", () => this.inspectNode(n));
      this.container.appendChild(g);
    });

    this.updateTransform();
  }

  inspectNode(node) {
    this.inspector.style.display = "block";
    document.getElementById("insp-id").textContent = node.id;
    document.getElementById("insp-lits").textContent = node.lits;
    document.getElementById("insp-ante").textContent = node.ante ? node.ante.join(", ") : "Axiom Input";
    document.getElementById("insp-pivot").textContent = node.pivot || "N/A";
    document.getElementById("insp-theory").textContent = node.isConflict ? "Conflict Clause" : "Derived Lemma";
  }
}

window.addEventListener("DOMContentLoaded", () => {
  new ProofVisualizer();
});
