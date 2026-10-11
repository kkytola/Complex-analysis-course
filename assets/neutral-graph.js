/* ============================================================================================
 * Presentation tweaks for the MS-C1300 course blueprint (Verso Blueprint). Companion of
 * neutral-graph.css (read its header for the background).
 *
 * WHAT IT DOES:
 *   1. Makes the graph page open in "Group View" (one box per chapter) instead of the illegible
 *      "Full Graph"; `?view=full` or `?view=parent:grp_<chapter>` in the URL overrides it.
 *   2. Adds a short hint paragraph above the graph.
 *   3. Removes formalization-status wording from the legend and from node tooltips (the project has
 *      no Lean formalization), and adds a legend entry for the chapter frames.
 *   4. Removes the "Lean status" chip from statement headers (the stylesheet hides it; this also removes its text
 *      from the page) and the "Lean" and "VersoBlueprint" tool-provenance entries of the build line on the root page.
 *
 * LOADED BY: ComplexAnalysisCourse/SiteConfig.lean: copied to <site>/assets/ and loaded by a plain
 * <script src="assets/neutral-graph.js"> in the <head> of every page. It must run before Verso Blueprint's
 * own page runtime initialises the graph; it does, because it registers its DOMContentLoaded listener
 * while the <head> is parsed, and the runtime (a module script) only starts later, after the d3 and
 * d3-graphviz libraries have loaded. On pages without a graph only item 4 does anything.
 *
 * UPSTREAM HOOKS THIS FILE DEPENDS ON (re-check after every VersoBlueprint upgrade):
 *   .bp_graph_fullwidth                          graph block
 *   select.bp_graph_view_select                  view selector; its value at start-up is the initial view
 *                                                (options: "full", "group", "parent:<group label>")
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

  // Initial view of the graph page: "group" (overview of the chapters), "full" (everything; huge)
  // or "parent:grp_<chapter label>" (one chapter).
  var DEFAULT_VIEW = "group";

  // Wording that must never be visible: anything that talks about formalization status.
  // Matching legend entries, tooltips etc. are removed or replaced.
  var BANNED = /status|blocked|ready|formali[sz]|\bLean\b|Mathlib|sorry|colou?rs?\b|warning|incomplete|declaration/i;

  var HINT =
    "Arrows point from a result to the statements that use it. The overview has one box per chapter: click a " +
    "chapter (or pick one in the View menu) to see its statements, and click a statement to read it. " +
    "The full graph of all statements is very large; zoom into it with the mouse wheel.";

  var FULL_NOTE =
    "Boxes are definitions; ellipses are theorems, lemmas and corollaries. A dashed frame groups the " +
    "statements of one chapter. The line style of an arrow tells whether the dependency occurs in the " +
    "statement itself or only in its proof.";

  var GROUP_NOTE =
    "Each tab is a chapter. An arrow between two chapters means that some statement of one chapter uses " +
    "a statement of the other. Click a chapter to see its statements.";

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

  /* ---- 1. Initial view ---------------------------------------------------------------------- */

  // The runtime starts in whatever view is selected in the <select> when it initialises the graph.
  function setInitialView(block) {
    var select = block.querySelector("select.bp_graph_view_select");
    if (!select) return;
    var wanted = DEFAULT_VIEW;
    try {
      wanted = new URLSearchParams(window.location.search).get("view") || DEFAULT_VIEW;
    } catch (_err) {}
    for (var i = 0; i < select.options.length; i++) {
      if (select.options[i].value === wanted) {
        select.value = wanted;
        return;
      }
    }
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

  function legendItem(group, label, swatchStyle) {
    var item = document.createElement("span");
    item.className = "bp_graph_legend_item";
    var swatch = document.createElement("span");
    swatch.className = "bp_graph_legend_swatch";
    swatch.setAttribute("style", swatchStyle);
    item.appendChild(swatch);
    item.appendChild(document.createTextNode(label));
    group.querySelector(".bp_graph_legend_items").appendChild(item);
  }

  function neutraliseLegend(block) {
    each(block.querySelectorAll(".bp_graph_legend"), function (legend) {
      var kind = legend.getAttribute("data-bp-legend-kind");
      var note = legend.querySelector(".bp_graph_legend_note");
      if (note && BANNED.test(note.textContent)) {
        note.textContent = kind === "group" ? GROUP_NOTE : FULL_NOTE;
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
      // Chapter frames (clusters) are part of the full graph: add the missing legend entry.
      if (kind === "full") {
        var shapes = legend.querySelector(".bp_graph_legend_group");
        if (shapes) {
          var frames = shapes.cloneNode(true);
          frames.querySelector(".bp_graph_legend_group_title").textContent = "Frames";
          var summary2 = frames.querySelector(".bp_graph_legend_group_summary");
          if (summary2) summary2.textContent = "Statements are grouped by chapter.";
          each(frames.querySelectorAll(".bp_graph_legend_item"), remove);
          legend.insertBefore(frames, shapes.nextSibling);
          legendItem(frames, "Chapter",
            "background: transparent; border-color: #cbd5e1; border-style: dashed; border-radius: 0.4rem");
        }
      }
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
    each(document.querySelectorAll(".bp_graph_fullwidth"), function (block) {
      setInitialView(block);
      addHint(block);
      neutraliseLegend(block);
      watchTitles(block);
    });
    removeLeanChips();
    trimBuildLine();
  });
})();
