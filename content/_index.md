---
title: null
type: landing
sections:
- block: about.avatar
  content:
    text: null
    username: admin
  id: about
- block: features
  content:
    items:
    - description:
      icon: r-project
      icon_pack: fab
      name: R
    - description:
      icon: python
      icon_pack: fab
      name: Python      
    - description:
      icon: chart-line
      icon_pack: fas
      name: Statistics
    title: Skills
- block: experience
  content:
    title: Experience    
    date_format: Jan 2006
    items:
    - title: Data Scientist
      company: Google
      company_url: ""
      location: 
      date_start: "2021-03-01"
      date_end: ""
      description: >
        DS for Google Payments     
    - title: Visiting Assistant Professor in Statistics
      company: University of California, Davis
      company_url: ""
      location: California
      date_start: "2019-09-01"
      date_end: "2021-03-01"
      description: >
        Teach upper division data science courses, e.g.
        Data & Web Technologies for Data Analysis
        Big Data & High Performance Statistical Computing
    - title: Assistant Professor in Statistics
      company: University of Maine
      company_url: ""
      location: Maine
      date_start: "2015-09-01"
      date_end: "2019-08-31"
      description: >
        Taught upper division statistics courses, e.g. <br>
        - Engineering Statistics<br>
        - Statistical Methods in Research<br>
        - Statistical Methods in Machine Learning
  design:
    columns: "2"
- block: collection
  content:
    count: 5
    filters:
      author: ""
      category: ""
      exclude_featured: false
      exclude_future: false
      exclude_past: false
      folders:
      - post
      publication_type: ""
      tag: ""
    offset: 0
    order: desc
    subtitle: ""
    text: ""
    title: Recent Posts
  design:
    columns: "2"
    view: compact
  id: posts
- block: portfolio
  content:
    buttons:
    - name: All
      tag: '*'
    - name: R
      tag: R
    - name: Python
      tag: Python
    default_button_index: 0
    filters:
      folders:
      - project
    title: Projects
    sort_by: Weight
  design:
    columns: "1"
    flip_alt_rows: true
    # view: showcase
  id: projects
---
