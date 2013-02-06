
# http://stackoverflow.com/questions/1263072/changing-a-matrix-from-right-handed-to-left-handed-coordinate-system

def toOtherHand(quatStr):
    (
        rx, ry, rz, _r,
        ux, uy, uz, _u, 
        lx, ly, lz, _l, 
        px, py, pz, _p, 
    )\
    = quatStr.split()

    return ' '.join(
    (
        rx, rz, ry, _r,
        lx, lz, ly, _l,
        ux, uz, uy, _u,
        px, pz, py, _p
    ))

orig = "1.000000 -0.000000 0.000000 19.524590 0.000000 1.000000 -0.000000 0.000000 0.000000 0.000000 1.000000 0.000000 0.000000 0.000000 0.000000 1.000000"

print toOtherHand(orig)
