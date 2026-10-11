/* ============================================================================================
 * Presentation tweaks for the MS-C1300 course blueprint (Verso Blueprint). Companion of
 * neutral-graph.css (read its header for the background).
 *
 * WHAT IT DOES:
 *   1. Draws the *transitive reduction* of the dependency graph: an arrow a -> b is left out when b can be
 *      reached from a through other arrows (the legacy leanblueprint page did the same with Graphviz `tred`;
 *      Verso Blueprint draws every dependency). Only the drawing changes: the "uses" / "used by" lists of
 *      the statements still show every dependency.
 *   2. Adds a short hint paragraph above the graph.
 *   3. Removes formalization-status wording from the legend and from node tooltips (the project has
 *      no Lean formalization).
 *   4. Removes the "Lean status" chip from statement headers (the stylesheet hides it; this also removes its text
 *      from the page) and the "Lean" and "VersoBlueprint" tool-provenance entries of the build line on the root page.
 *   0. Sets the page language (Verso emits <html> without `lang`; screen readers need it).
 *
 * LOADED BY: ComplexAnalysisCourse/SiteConfig.lean: copied to <site>/assets/ and loaded by a plain
 * <script src="assets/neutral-graph.js"> in the <head> of every page. It must run before Verso Blueprint's
 * own page runtime initialises the graph; it does, because it registers its DOMContentLoaded listener
 * while the <head> is parsed, and the runtime (a module script) only starts later, after the d3 and
 * d3-graphviz libraries have loaded. On pages without a graph only item 4 does anything.
 *
 * UPSTREAM HOOKS THIS FILE DEPENDS ON (re-check after every VersoBlueprint upgrade):
 *   .bp_graph_fullwidth                          graph block
 *   script.bp-graph-data                         JSON of the graph block: variants[].dot = Graphviz source of each view,
 *                                                one edge per line:   "a" -> "b" [style=...];
 *   .bp_graph_legend[data-bp-legend-kind]        legend ("full" / "group"), static HTML
 *   .bp_graph_legend_note / _group / _group_title / _group_summary / _items / _item / _swatch
 *   SVG elements below .bp_graph_fullwidth       d3-graphviz output; tooltips are `title`/`xlink:title` attributes
 *   .bp_extra_slot_code, .bp_code_summary_preview_panel   the "Lean status" chip slot in statement headers and its hover panel
 *   .bp_build_metadata_item > .bp_build_metadata_label    root-page build line
 * Texts below are in English only, like the rest of the site.
 * ============================================================================================ */
(function () {
  "use strict";

  /* ---- Settings ---------------------------------------------------------------------------- */

  // Wording that must never be visible: anything that talks about formalization status.
  // Matching legend entries, tooltips etc. are removed or replaced.
  var BANNED = /status|blocked|ready|formali[sz]|\bLean\b|Mathlib|sorry|colou?rs?\b|warning|incomplete|declaration/i;

  var HINT =
    "Arrows point from a result to the statements that use it. An arrow is left out when the same dependency " +
    "already follows from other arrows (every dependency is listed in the statement headers). Click a " +
    "statement to read it; zoom with the mouse wheel and pan by dragging.";

  var FULL_NOTE =
    "Boxes are definitions; ellipses are theorems, lemmas and corollaries. The line style of an arrow tells " +
    "whether the dependency occurs in the statement itself or only in its proof. Arrows that follow from " +
    "other arrows are not drawn.";

  /* ---- Helpers ------------------------------------------------------------------------------ */

  function onReady(fn) {
    if (document.readyState === "loading") {
      document.addEventListener("DOMContentLoaded", fn);
    } else {
      fn();
    }
  }

  function each(list, fn) {
    Array.prototype.forEach.call(list, fn);
  }

  function remove(el) {
    if (el && el.parentNode) el.parentNode.removeChild(el);
  }

  /* ---- 1. Transitive reduction ---------------------------------------------------------------- */

  // One edge per line, as emitted by Verso Blueprint:   "a" -> "b" [style=dashed, penwidth=1.2];
  var EDGE_RE = /^\s*"((?:[^"\\]|\\.)*)"\s*->\s*"((?:[^"\\]|\\.)*)"/;

  // Remove from a Graphviz source every edge a -> b such that b is reachable from a through another
  // successor of a. Returns the source unchanged if there is no edge or the graph has a cycle.
  function reduceDot(dot) {
    var lines = dot.split("\n");
    var edges = [];
    var succ = Object.create(null);
    lines.forEach(function (line, i) {
      var m = EDGE_RE.exec(line);
      if (!m) return;
      edges.push({ line: i, from: m[1], to: m[2] });
      (succ[m[1]] = succ[m[1]] || []).push(m[2]);
    });
    if (edges.length === 0) return dot;

    var memo = Object.create(null); // node -> set of nodes reachable by a path of length >= 1
    var state = Object.create(null); // 1 = on the DFS stack, 2 = done
    var cyclic = false;
    function reach(u) {
      if (memo[u]) return memo[u];
      if (state[u] === 1) { cyclic = true; return Object.create(null); }
      state[u] = 1;
      var set = Object.create(null);
      (succ[u] || []).forEach(function (w) {
        set[w] = true;
        var r = reach(w);
        for (var k in r) set[k] = true;
      });
      state[u] = 2;
      memo[u] = set;
      return set;
    }

    var drop = Object.create(null);
    edges.forEach(function (e) {
      succ[e.from].forEach(function (w) {
        if (w !== e.to && reach(w)[e.to]) drop[e.line] = true;
      });
    });
    if (cyclic) return dot;
    return lines.filter(function (_line, i) { return !drop[i]; }).join("\n");
  }

  // The page embeds the graph as JSON in <script type="application/json" class="bp-graph-data">; the page
  // runtime draws the Graphviz source of the selected view (variants[].dot) from it. Rewrite that source.
  function reduceGraphData() {
    each(document.querySelectorAll("script.bp-graph-data"), function (script) {
      if (script.getAttribute("data-cac-reduced")) return;
      var data;
      try { data = JSON.parse(script.textContent); } catch (_err) { return; }
      if (!data || !Array.isArray(data.variants)) return;
      data.variants.forEach(function (variant) {
        if (typeof variant.dot === "string") variant.dot = reduceDot(variant.dot);
      });
      script.textContent = JSON.stringify(data);
      script.setAttribute("data-cac-reduced", "1");
    });
  }

  /* ---- 2. Hint above the graph -------------------------------------------------------------- */

  function addHint(block) {
    if (!block.parentNode || document.querySelector(".cac-graph-hint")) return;
    var p = document.createElement("p");
    p.className = "cac-graph-hint";
    p.textContent = HINT;
    block.parentNode.insertBefore(p, block);
  }

  /* ---- 3. Legend and tooltips --------------------------------------------------------------- */

  function neutraliseLegend(block) {
    each(block.querySelectorAll(".bp_graph_legend"), function (legend) {
      var note = legend.querySelector(".bp_graph_legend_note");
      if (note && BANNED.test(note.textContent)) {
        note.textContent = FULL_NOTE;
      }
      each(legend.querySelectorAll(".bp_graph_legend_group"), function (group) {
        each(group.querySelectorAll(".bp_graph_legend_item"), function (item) {
          if (BANNED.test(item.textContent)) remove(item);
        });
        var title = group.querySelector(".bp_graph_legend_group_title");
        var summary = group.querySelector(".bp_graph_legend_group_summary");
        if (summary && BANNED.test(summary.textContent)) remove(summary);
        var empty = !group.querySelector(".bp_graph_legend_item");
        if (empty || (title && BANNED.test(title.textContent))) remove(group);
      });
    });
  }

  // Tooltips of graph nodes ("Statement: blocked | Proof: not ready") are `title` / `xlink:title`
  // attributes that d3-graphviz creates whenever it renders a view (also in the group preview panel).
  function scrubTitles(root) {
    var els = root.querySelectorAll("[title], [*|title]");
    each(els, function (el) {
      each(Array.prototype.slice.call(el.attributes), function (attr) {
        if (attr.localName === "title" && BANNED.test(attr.value)) el.removeAttributeNode(attr);
      });
    });
  }

  function watchTitles(block) {
    scrubTitles(block);
    if (typeof MutationObserver !== "function") return;
    new MutationObserver(function (records) {
      each(records, function (record) {
        each(record.addedNodes, function (node) {
          if (node.nodeType === 1) {
            scrubTitles(node);
            // the node itself (querySelectorAll only looks at descendants)
            each(Array.prototype.slice.call(node.attributes), function (attr) {
              if (attr.localName === "title" && BANNED.test(attr.value)) node.removeAttributeNode(attr);
            });
          }
        });
      });
    }).observe(block, { childList: true, subtree: true });
  }

  /* ---- 4. Lean chip and build line --------------------------------------------------------- */

  function removeLeanChips() {
    // the chip slot, and its hover panel which the page runtime has appended to <body>
    each(document.querySelectorAll(".bp_extra_slot_code, .bp_code_summary_preview_panel"), remove);
  }

  function trimBuildLine() {
    each(document.querySelectorAll(".bp_build_metadata_item"), function (item) {
      var label = item.querySelector(".bp_build_metadata_label");
      if (label && /^(Lean|VersoBlueprint)$/.test(label.textContent.trim())) remove(item);
    });
  }

  /* ---- Main --------------------------------------------------------------------------------- */

  onReady(function () {
    if (!document.documentElement.getAttribute("lang")) document.documentElement.setAttribute("lang", "en");
    reduceGraphData();
    each(document.querySelectorAll(".bp_graph_fullwidth"), function (block) {
      addHint(block);
      neutraliseLegend(block);
      watchTitles(block);
    });
    removeLeanChips();
    trimBuildLine();
  });
})();
