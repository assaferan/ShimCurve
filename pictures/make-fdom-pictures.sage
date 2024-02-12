#Code to make the png images of fundamental domains. Modified based on David Lowry-Duda's LMFDB code.
gp.read("fdom.gp")
from sage.misc.decorators import options, rename_keyword
from sage.plot.hyperbolic_polygon import HyperbolicPolygon
from sage.libs.pari.convert_sage import gen_to_sage


#SECTION 1: GRAPHICS


#To encode the png file as a string.
def encode_mcurve_plot(P, transparent=True):
    from io import BytesIO as IO
    from matplotlib.backends.backend_agg import FigureCanvasAgg
    from base64 import b64encode
    from urllib.parse import quote

    virtual_file = IO()
    fig = P.matplotlib(axes_pad=None)
    ax = fig.axes[0]
    ax.set_xlim(xmin=-1, xmax=1)
    ax.set_ylim(ymin=-1, ymax=1)
    fig.set_canvas(FigureCanvasAgg(fig))
    fig.set_size_inches(2.5, 2.5) # images are 200 x 200 on the website
    fig.savefig(virtual_file, format='png', bbox_inches='tight', transparent=transparent, dpi=120)
    virtual_file.seek(0)
    buf = virtual_file.getbuffer()
    return "data:image/png;base64," + quote(b64encode(buf))

#To make a hyperbolic polygon given the vertices.
@rename_keyword(color='rgbcolor')
@options(alpha=1, fill=True, thickness=0, rgbcolor="blue", zorder=2, linestyle='solid')
def my_hyperbolic_polygon(pts, model="PD", resolution=200, circlecolor='black', add_circle=False, **options):
    r"""
    Return a hyperbolic polygon in the hyperbolic plane with vertices ``pts``.

    This is on the poincare disk, but doesn't add random black circles
    repeatedly like the default version.

    INPUT:

    - ``pts`` -- a list or tuple of complex numbers

    OPTIONS:

    - ``alpha`` -- default: 1

    - ``fill`` -- default: ``False``

    - ``thickness`` -- default: 1

    - ``rgbcolor`` -- default: ``'blue'``

    - ``linestyle`` -- (default: ``'solid'``) the style of the line, which is
      one of ``'dashed'``, ``'dotted'``, ``'solid'``, ``'dashdot'``, or
      ``'--'``, ``':'``, ``'-'``, ``'-.'``, respectively
    """
    if not model == "PD":
        raise ValueError("Only the disk model is supported")
    from sage.plot.all import Graphics
    g = Graphics()
    g._set_extra_kwds(g._extract_kwds_for_show(options))

    g.add_primitive(HyperbolicPolygon(pts, model, options))
    g.set_aspect_ratio(1)
    if add_circle:
        g = g + circle((0, 0), 1, rgbcolor=circlecolor)
    return g

#Given the vertices for one fundamental domain, makes the domain as a Graphics object.
def onefdomgraphicsobject(verts):
    g = Graphics()
    g += my_hyperbolic_polygon(verts, add_circle = True);
    g.axes(False)
    g.set_axes_range(-1, 1, -1, 1)
    return g


#SECTION 2: FUNDAMENTAL DOMAINS


#Return the fundamental domain for D
def level1fdom(D):
    gp.setrand(1)
    A = gp.alginit_Qdisc(D)
    gp.setrand(1)
    X = gp.afuchinit(A);
    return X
    
#Make the level 1 pictures for all D in Dlist. We need to also input the size of Aut_mu(O), so the pairs are [D, #Aut_mu] where mu is a degree 1 polarization.
def make_pictures_level1(Dlistwithmu):
    fil = open("../data/level1_pictures.fdom", "a")
    for pair in Dlistwithmu:
        D = pair[0]
        sizeautmu = pair[1]
        X = level1fdom(D)
        verts = gen_to_sage(pari(gp.afuchvertices(X, 1)));
        g = onefdomgraphicsobject(verts)
        genus = gp.afuchsignature(X)[1]
        pngstr = encode_mcurve_plot(g)
        fil.write(f"{D}.1.1.{sizeautmu}.{genus}.a.1?{pngstr}\n")
    fil.close()

