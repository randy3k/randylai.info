+++
headless = true  # This file represents a page section.
active = true  # Activate this widget? true/false
weight = 90  # Order that this section will appear.

title = "Publications"
subtitle = ""
+++

<bibtex src="pub.bib"></bibtex>

<div class="bibtex_display", year="[0-9+]"></div>
<div class="bibtex_template", style="display: none">
  <div style="font-weight: bold;">
    <span class="author"></span>
    <span class="if year">
      (<span class="year"></span>),&nbsp
    </span>
  </div>
  <div style="margin-left: 10px; margin-bottom:5px;">
  <a class="url"><span class="title"></span></a>,&nbsp
  <span class="if journal">
    <span class="if !(volume || pages)">
      <span class="journal" style="font-style: italic;"></span>.
    </span>
    <span class="if volume || pages">
      <span class="journal" style="font-style: italic;"></span>,
    </span>
  </span>
  <span class="if volume">
    <span class="if !pages">
      <span class="volume"></span>.
    </span>
    <span class="if pages">
      <span class="volume"></span>,
    </span>
  </span>
  <span class="if pages">
    <span class="pages"></span>.
  </span>
  </div>
</div>
