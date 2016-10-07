from regina import *
def make_dipyr(n):
        """Returns an n-dipyr."""
        newt = NTriangulation()
        for i in range(0,n):
                newt.newTetrahedron()
        for i in range(0,n):
                me = newt.getTetrahedron(i)
                you = newt.getTetrahedron((i+1)%n)
                me.joinTo(2,you,NPerm4(2,3))
        return newt
def which_tet(n,face):
    if face < n:
        return face
    else:
        return face - n

def make_necklace(fpfinv):
    n = len(fpfinv)
    ndipyr = make_dipyr(n)
    local = list(fpfinv)
    while local != []:
        (i,j) = local.pop()
        me = ndipyr.getTetrahedron(which_tet(n,i))
        you = ndipyr.getTetrahedron(which_tet(n,j))
        if i < n:
                f = 0
        else:
                f = 1
        if ((i < n) == (j < n)):
            me.joinTo(f,you,NPerm4(2,3))
        else:
            me.joinTo(f,you,NPerm4(0,1))
    ndipyr.setPacketLabel(str(fpfinv))
    return ndipyr
def rt(n,t,face):
    if face < n:
        if face + t < n:
            return face + t
        else:
            return face + t - n
    else:
        if face + t < 2 * n:
            return face + t
        else:
            return face + t - n

def p_fl(n,face):
    if face < n:
        return face + n
    else:
        return face - n

def v_fl(n,face):
    if face < n:
        return n - (face + 1)
    else:
        return (3 * n) - (face + 1)
def act_face (n,dp,face):
    (s,t) = dp
    r = rt(n,t,face)
    if s == "Rot":
        return r
    if s == "VRot":
        return v_fl(n,r)
    if s == "PRot":
        return p_fl(n,r)
    if s == "VPRot":
        return v_fl(n,p_fl(n,r))
    else:
        raise Exception
def act_face_pair(n,dp,facepair):
    (i,j) = facepair
    a_f = act_face
    (x,y) = (a_f (n,dp,i), a_f(n,dp,j))
    if x > y:
        return (x,y)
    else:
        return (y,x)
def act_gluing(n,dp,gluing):
    afp = act_face_pair
    unsorted = map((lambda fp: afp(n,dp,fp)), \
                                 gluing)
    return sorted(unsorted, reverse=True)
def orbit_with_repeats(n,gluing):
    l = gluing
    nums = range(n)
    nums.reverse()
    ag = act_gluing
    symm_types = ["Rot","VRot","PRot","VPRot"]
    out = []
    for s in symm_types:
        for t in nums:
            out = [ag(n,(s,t),l)] + out
    return out
def smush (l,m):
    if m == []:
        return l
    else:
        return smush (([m[0]] + l), m[1:])

def fpf(l,m):
    if l == []:
        return ("PTLeaf",)
    # else
    f = l[0]
    lp = l[1:]
    if lp == []:
        return ("PTLeaf",)
    fp = l[1]
    lpp = l[2:]
    return ("PTBranch", \
            (f,fp), \
            fpf(smush(lpp,m), []), \
            fpf([f] + lpp, [fp] + m))
    
def original_tree(n):
    nums = range(2*n)
    nums.reverse()
    return fpf(nums, [])
def get_left_inv(pt):
    if pt[0] == "PTLeaf":
        return []
    else:
        (str, p, lt, rt) = pt
        assert str == "PTBranch"
        return [p] + get_left_inv(lt)
def remove_involution(l,pt):
    if l == []:
        return pt
    if pt[0] == "PTLeaf":
        return pt
    p,ps,(str,pp,lt,rt) = l[0],l[1:],pt
    assert str == "PTBranch"
    if p != pp:
        return ("PTBranch", pp, lt, \
                remove_involution(l,rt))
    ltp = remove_involution(ps,lt)
    if ltp[0] == "PTLeaf":
        return rt
    else:
        return ("PTBranch", pp, ltp, rt)
def orbit_reps(n):
    pt = original_tree(n)
    reps = []
    while pt[0] != "PTLeaf":
        l = get_left_inv(pt)
        reps = [l] + reps
        lorb = orbit_with_repeats(n,l)
        for lp in lorb:
             pt = remove_involution(lp,pt)
    return reps
def link_complement(mfld):
    vs = mfld.vertices()
    for v in vs:
        if not (v.link() == v.TORUS):
            return False
    else:
        return True
def slow_connect_sum(regina_mfld):
    M = NTriangulation(regina_mfld)
    if not M.isConnected():
        raise Exception("Not connected")
    if not M.isOrientable():
        raise Exception("Not orientable")
    if not link_complement(M):
        raise Exception("Not a generalized link complement")
    nsl = NNormalSurfaceList.enumerate
    l = nsl(M, NS_STANDARD, \
               NS_FUNDAMENTAL)
    n = l.getNumberOfSurfaces()
    for i in range(0,n):
        s = l.getSurface(i)
        x = s.eulerChar()
        if x != 2:
            if x != 1:
                continue
            if s.isOrientable():
                continue
            raise Exception("P^2!")
        m = s.cutAlong()
        m.finiteToIdeal()
        m.intelligentSimplify()
        if m.isConnected():
            raise Exception("Non-separating S^2!")
        m.splitIntoComponents()
        m0 = m.getFirstTreeChild()
        m1 = m0.getNextTreeSibling()
        if not (m0.isThreeSphere() or \
                m1.isThreeSphere()):
            return slow_connect_sum(m0) + \
                   slow_connect_sum(m1)
    if M.isThreeSphere():
        return []
    else:
        return [M]

def vet_reds(sane_mflds):
    oks = []
    bads = []
    for i in range(len(sane_mflds)):
        mfld = sane_mflds[i]
        try:
            csd = slow_connect_sum(mfld)
            oks = [((i,mfld),csd)] + oks
        except:
            bads = [(i,mfld)] + bads
    return (oks,bads)
from new_unhyp import new_isT2xI as isT2xI
def cut_essential_tori(regina_mfld, loc):
    print loc
    M = NTriangulation(regina_mfld)
    M.finiteToIdeal()
    M.intelligentSimplify()
    nsl = NNormalSurfaceList.enumerate
    l = nsl(M, NS_STANDARD, \
                         NS_FUNDAMENTAL)
    n = l.getNumberOfSurfaces()
    print "There are " + str(n) + " surfaces"
    for i in range(0,n):
        print "Working on surface " + str(i)
        s = l.getSurface(i)
        x = s.eulerChar()
        if x != 0:
            continue
        if s.hasRealBoundary():
            continue
        if not s.isOrientable():
            raise Exception("K^2!")
        if s.isVertexLinking():
            continue
        m = s.cutAlong()
        if m.isConnected():
            raise Exception("Non-separating T^2!")
        m.finiteToIdeal()
        m.intelligentSimplify()
        m.splitIntoComponents()
        m0 = m.getFirstTreeChild()
        m1 = m0.getNextTreeSibling()
        print "Left solid torus?"
        if m0.isSolidTorus():
            continue
        print "Right solid torus?"
        if m1.isSolidTorus():
            continue
        print "Left T2 x I?"
        if isT2xI(m0):
            continue
        print "Right T2 x I?"
        if isT2xI(m1):
            continue
        return (cut_essential_tori(m0, loc+"L"), \
                        cut_essential_tori(m1, loc+"R"))
    else:
        return (M,)
def vet_tor(idx_irreds):
    cut_mflds = []
    bad_mflds = []
    for p in idx_irreds:
        (i,m) = p
        print str(i)
        try:
             cut_up = cut_essential_tori(m,".")
             cut_mflds = [(i,cut_up)] + cut_mflds
        except Exception as uh_oh:
            s = ["P^2!", "K^2!"]
            s = s + ["Non-separating S^2!"]
            s = s + ["Non-separating T^2!"]
            if uh_oh.message in s:
                bad_mflds = [(i,m,uh_oh.message)] + bad_mflds
            else:
                raise Exception(uh_oh.message)
    return (cut_mflds, bad_mflds) 
from new_unhyp import findNonSeparatingAnnulus
from snappy import *
def hyp_or_SFS(atoroidals):
    hyps = []
    sfss = []
    for p in atoroidals:
        (i,(m,)) = p
        print "Working on " + str(i)
        if m.hasStrictAngleStructure():
            hyps = [p] + hyps
            continue
        m.idealToFinite()
        m.intelligentSimplify()
        a = findNonSeparatingAnnulus(m)
        if a == None:
            hyps = [p] + hyps
            continue
        else:
            sfss = [(a,p)] + sfss
            continue
    return (hyps, sfss)
