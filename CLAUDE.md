# dprn.github.io

Personal academic website, built on the Start Bootstrap "Resume" template (the
`README.md` is the template's own). It is plain HTML: `index.html` holds the
bio, students, publications and CV link, `teaching.html` the courses, and
`docs/` the PDFs they link to. There is no build step for content edits.

## Adding a publication

Publications are `<li>` items in `index.html`, grouped under headings
(Preprints, refereed journals, conferences, …). The newest entry goes at the top
of its list, in this form:

```html
<li>
  <a href="https://arxiv.org/abs/2611.09188">
    Controlled Excitation for Identification of Nonlinear Systems with Saturated Outputs
  </a>
  <p>Adel Malik Annabi, Jean-Baptiste Pomet, Dario Prandi, and Ludovic Sacchelli</p>
</li>
```

Authors are in paper order, full names, with an Oxford comma before "and". When
a preprint is accepted, move it to the journals list and prefix the venue with
"To appear on".

## The CV PDF

`docs/cv_dario_prandi.pdf` is a copy of the English CV built in the sibling
folder `../CV/`, a separate git repo (`dprn/CV` on GitHub, `prandi/cv` on
GitLab). Every change to publications, students or teaching on the site should
be mirrored there, in both CVs:

1. Add the entry to `../CV/bib_dario_prandi.bib`, at the top of the file. A
   preprint is `@preprint` with `eprint`, `eprinttype = {arXiv}`, `eprintclass`,
   `doi`, `url` and `pubstate = {prepublished}`. Keys look like
   `AnnabiPometEtAl2026`.
2. Add a `\nocite{<key>}` to the right `refsection` in both
   `cv_dario_prandi.tex` and `cv_dario_prandi_fr.tex` (preprints are in the
   first block of the Publications section, newest first).
3. Update `\adcvdate{…}` in both files (English and French month names).
4. Build both with `latexmk cv_dario_prandi.tex` and
   `latexmk cv_dario_prandi_fr.tex` (XeLaTeX and biber, configured in
   `.latexmkrc`). The biber warnings about `to appear` years are old and
   harmless.
5. Commit in `../CV/` (sources and both PDFs), then copy
   `../CV/cv_dario_prandi.pdf` to `docs/` here and commit it with the
   `index.html` change.

## Profile photo

`img/profile.jpg` (shown in a circle on `index.html` and `teaching.html`) is a
600 × 600 copy of the CV photo `../CV/dario.jpg`. The crop is documented in
`../CV/CLAUDE.md`. Change both together.
