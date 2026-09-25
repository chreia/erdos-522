# Shared style for all paper figures: Latin Modern text, Computer Modern math,
# a small thermal-derived palette, and print-appropriate line weights.
import glob, os, subprocess
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib import font_manager
INK='#000000'; INK2='#4a4a48'; MUTED='#8a8983'; RULE='#d9d8d3'
PURPLE='#5b43a8'; ORANGE='#d9602e'; NAVY='#1f2a5a'
PURPLE_TINT='#ebe7f6'; ORANGE_TINT='#fbe9df'; GREY_TINT='#f3f2ef'
# Okabe-Ito blue, its 45% tint and a light wash, as in the tilted-mean figure.
OI_BLUE='#0072B2'; OI_BLUE_TINT='#8CC0DC'; OI_BLUE_WASH='#E0EEF6'
LW_DATA=1.1; LW_THEORY=0.85; LW_CONSTR=1.0; LW_FINE=0.6; MS=3.4
def lm_dir():
    '''Directory of the Latin Modern OpenType fonts, found through kpsewhich when possible.'''
    cands = []
    try:
        p = subprocess.run(['kpsewhich', 'lmroman10-regular.otf'], capture_output=True, text=True).stdout.strip()
        if p: cands.append(os.path.dirname(p))
    except OSError:
        pass
    cands += ['/usr/share/texmf/fonts/opentype/public/lm', '/usr/share/texlive/texmf-dist/fonts/opentype/public/lm']
    for c in cands:
        if os.path.isdir(c): return c
    raise FileNotFoundError('Latin Modern OpenType fonts not found')
def _otf_to_ttf(src, dst, family):
    """Convert a CFF OpenType font to TrueType outlines, so that pdf.fonttype 42 embeds it correctly."""
    from fontTools.ttLib import TTFont, newTable
    from fontTools.pens.cu2quPen import Cu2QuPen
    from fontTools.pens.ttGlyphPen import TTGlyphPen
    font = TTFont(src)
    order = font.getGlyphOrder(); gs = font.getGlyphSet(); glyphs = {}
    for name in order:
        pen = TTGlyphPen(gs)
        gs[name].draw(Cu2QuPen(pen, max_err=1.0, reverse_direction=True))
        glyphs[name] = pen.glyph()
    font['loca'] = newTable('loca')
    font['glyf'] = glyf = newTable('glyf')
    glyf.glyphOrder = order; glyf.glyphs = glyphs
    del font['CFF ']
    if 'VORG' in font: del font['VORG']
    glyf.compile(font)
    hmtx = font['hmtx']
    for name, g in glyf.glyphs.items():
        if hasattr(g, 'xMin'): hmtx[name] = (hmtx[name][0], g.xMin)
    font['maxp'] = maxp = newTable('maxp')
    maxp.tableVersion = 0x00010000
    for k in ('maxZones', 'maxTwilightPoints', 'maxStorage', 'maxFunctionDefs', 'maxInstructionDefs',
              'maxStackElements', 'maxSizeOfInstructions', 'maxComponentElements'):
        setattr(maxp, k, 1 if k == 'maxZones' else 0)
    maxp.compile(font)
    post = font['post']; post.formatType = 2.0; post.extraNames = []; post.mapping = {}; post.glyphOrder = order
    font['head'].glyphDataFormat = 0
    font.sfntVersion = '\x00\x01\x00\x00'
    for rec in font['name'].names:       # a family name of its own, so no other optical size is chosen
        if rec.nameID in (1, 16):
            rec.string = family
    font.save(dst)
ROMAN, MONOFAM = 'LM Roman 10 TT', 'LM Mono 10 TT'
def lm_font(name):
    """Path of a TrueType copy of a Latin Modern font, converted once and cached."""
    cache = os.path.join(os.path.expanduser('~'), '.cache', 'erdos522-latin-modern')
    os.makedirs(cache, exist_ok=True)
    dst = os.path.join(cache, name.replace('.otf', '-tt.ttf'))
    if not os.path.exists(dst):
        _otf_to_ttf(os.path.join(lm_dir(), name), dst, MONOFAM if 'mono' in name else ROMAN)
    return dst
def setup():
    for f in sorted(glob.glob(os.path.join(lm_dir(), 'lmroman10-*.otf'))):
        font_manager.fontManager.addfont(lm_font(os.path.basename(f)))
    plt.rcParams.update({
        'font.family':ROMAN,'mathtext.fontset':'cm','axes.formatter.use_mathtext':True,
        'axes.unicode_minus':True,'font.size':9,'axes.labelsize':9,'axes.titlesize':9.5,
        'xtick.labelsize':8.5,'ytick.labelsize':8.5,'legend.fontsize':8.5,'legend.frameon':False,
        'axes.spines.top':False,'axes.spines.right':False,'axes.linewidth':0.6,'axes.edgecolor':INK2,
        'axes.labelcolor':INK,'text.color':INK,'xtick.color':INK2,'ytick.color':INK2,'xtick.labelcolor':INK,'ytick.labelcolor':INK,
        'xtick.major.width':0.6,'ytick.major.width':0.6,'xtick.major.size':3,'ytick.major.size':3,
        'xtick.minor.width':0.4,'ytick.minor.width':0.4,'xtick.minor.size':1.8,'ytick.minor.size':1.8,
        'lines.linewidth':LW_DATA,'lines.markersize':MS,'axes.grid':False,
        'pdf.fonttype':42,'savefig.dpi':600,'figure.dpi':150})
def title(ax,letter,text,**kw):
    ax.text(0,1.045,(r'$\mathbf{%s}$' % letter)+'  '+text,transform=ax.transAxes,fontsize=9.5,va='bottom',ha='left',**kw)
