+++
headless = true  # This file represents a page section.
active = true  # Activate this widget? true/false
weight = 90  # Order that this section will appear.

title = "Publications"
subtitle = ""

[design]
  columns = "1"
+++

<script type="text/javascript" src="https://cdn.jsdelivr.net/gh/pcooksey/bibtex-js/src/bibtex_js.js"></script>

<bibtex src="pub.bib"></bibtex>

<div class="bibtex_display", year="[0-9+]">
<div class="bibtex_template", style="display: none">
  <div class="if author" style="font-weight: bold;">
    <span class="if year">
      <span class="year"></span>, 
    </span>
    <span class="author"></span>
  </div>
  <div style="margin-left: 10px; margin-bottom:5px;">
    <span class="title"></span>,
    <span class="if journal">
    <i><span class="journal"></span></i>
  </span>
  </div>
</div>
</div>
