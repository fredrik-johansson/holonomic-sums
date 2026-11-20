"""
Build a preview of zetaF.tex in the style of Annales Henri Lebesgue (cedram class).

The cedram class files (cedram.cls, cedram-AHL.clo, cedram-AHL.sty, cedram-style.sty,
cedram-util.sty, amsalpha+eid.bst, logoAHL.pdf, logo_Mersenne-nb.png, cc-by.pdf) are not
part of the repository; download AHL.zip from https://annales.lebesgue.fr (FAQ page) and
unpack it into paper/ahl/cedram/ (or pass another directory as the first argument).
The class needs the LaTeX packages babel-french and lmodern.

Usage (from any directory):  python3 paper/ahl/make_ahl.py [cedram_dir]
Output: paper/ahl/build/zetaF-ahl.pdf

Only the preamble and front matter are changed: document class, author/title/abstract
macros in cedram form, a French title and abstract, the cedram theorem environments
(only Theorem A/B and Claim C are defined here), \\todo (predefined by the class) and a
blank line between \\bibitem entries (needed by the class's back-references).
"""
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
INPUTS = ['zetaF.tex', 'khinchin_listing.tex', 'khinchin_ref.py', 'khcf_gm.dat']

PREAMBLE = r'''\pdfoutput=1
\documentclass[AHL,XML,longabstracts,Unicode]{cedram}
\usepackage{booktabs}
\usepackage{xurl}
\usepackage{pgfplots}
\usepackage{listings}
\pgfplotsset{compat=1.18}

\DOI{10.NNNN/ahl.XXXX}

\AtBeginDocument{%
\newtheorem*{theoremA}{Theorem A}%
\newtheorem*{theoremB}{Theorem B}%
\newtheorem*{claimC}{Claim C}%
}

<macros>
\author[\initial{F.} \lastname{Johansson}]{\firstname{Fredrik} \lastname{Johansson}}
\address{INRIA, Universit\'{e} de Bordeaux, CNRS, CANARI, 33400 Talence, France}
\email{fredrik.johansson@gmail.com}

\title[Infinite sums of holonomic functions]{Computing infinite sums of holonomic functions}
\alttitle{Calcul de sommes infinies de fonctions holonomes}

<abstract>
\begin{altabstract}
Pour une fonction holonome $F$ r\'eguli\`ere \`a l'infini, nous \'etudions la fonction z\^eta
$\zeta_F(s) = \sum_{k}F(k)k^{-s}$. Nous montrons que lorsque le d\'eveloppement de $F$ \`a l'infini
a des coefficients alg\'ebriques, les valeurs et les d\'eriv\'ees de $\zeta_F$ en des points $s$
alg\'ebriques peuvent \^etre calcul\'ees \`a $p$ bits pr\`es en $p^{3/2+o(1)}$ op\'erations binaires.
Ceci donne des algorithmes sous-quadratiques pour une large classe de nombres, dont toute somme
$\sum_k A(k)$ ou $\sum_k \log A(k)$ o\`u $A$ est une fonction alg\'ebrique \`a coefficients
alg\'ebriques ; pour la plupart d'entre eux, aucun algorithme de complexit\'e meilleure que
quadratique n'\'etait connu. Nous donnons plusieurs exemples, dont le premier algorithme
sous-quadratique pour la constante de Khintchine, que nous calculons \`a $10^7$ chiffres.
\end{altabstract}

\subjclass{<subj>}
\keywords{<kw>}

\raggedbottom
\setlength{\emergencystretch}{1em}
'''


def take(pattern, body, flags=0):
    """Remove the first match of pattern from body; return (match, body)."""
    m = re.search(pattern, body, flags)
    return m, body.replace(m.group(0), '', 1)


def convert(src, dst):
    t = open(src).read()
    pre, body = t.split('\\begin{document}', 1)
    # abstract, MSC codes and keywords move from the body to the preamble
    m, body = take(r'\\begin\{abstract\}.*?\\end\{abstract\}\n', body, re.S)
    abstract = m.group(0)
    m, body = take(r'\\subjclass(\[2020\])?\{(.*?)\}\n', body)
    subj = m.group(2)
    m, body = take(r'\\keywords\{(.*?)\}\n', body)
    kw = m.group(1)
    macros = pre[pre.index('\\newcommand{\\erfc}'):pre.index('\\title')]
    macros = macros.replace('\\newcommand{\\todo}', '\\renewcommand{\\todo}')
    # the class's back-references need a \par after each \bibitem
    i = body.index('\\begin{thebibliography}')
    j = body.index('\\end{thebibliography}')
    body = body[:i] + body[i:j].replace('\n\\bibitem', '\n\n\\bibitem') + '\n' + body[j:]
    out = PREAMBLE
    for key, val in [('macros', macros), ('abstract', abstract), ('subj', subj), ('kw', kw)]:
        out = out.replace('<%s>' % key, val)
    open(dst, 'w').write(out + '\\begin{document}' + body)


def main():
    cls = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.join(HERE, 'cedram')
    if not os.path.exists(os.path.join(cls, 'cedram.cls')):
        sys.exit('cedram.cls not found in %s (see the docstring of this script)' % cls)
    build = os.path.join(HERE, 'build')
    os.makedirs(build, exist_ok=True)
    for f in os.listdir(cls):
        shutil.copy(os.path.join(cls, f), build)
    for f in INPUTS:
        shutil.copy(os.path.join(PAPER, f), build)
    convert(os.path.join(build, 'zetaF.tex'), os.path.join(build, 'zetaF-ahl.tex'))
    for _ in range(3):
        r = subprocess.run(['pdflatex', '-interaction=nonstopmode', 'zetaF-ahl.tex'],
                           cwd=build, stdout=subprocess.DEVNULL)
    if r.returncode:
        sys.exit('pdflatex failed; see %s' % os.path.join(build, 'zetaF-ahl.log'))
    print(os.path.join(build, 'zetaF-ahl.pdf'))


if __name__ == '__main__':
    main()
