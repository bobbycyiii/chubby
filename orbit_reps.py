def rt(n,t,m) :
  if m < n:
    if m + t < n:
      return m + t
    else:
      return m + t - n
  else:
    if m + t < 2 * n:
      return m + t
    else:
      return m + t - n

def rot(n) :
  return (lambda t: (lambda m: rt(n,t,m)))

def p_fl (n,m) :
  if m < n:
    return m + n
  else:
    return m - n

def p_flip(n):
  return (lambda m: p_fl(n,m))

def v_fl (n,m) :
  if m < n:
    return n - (m + 1)
  else:
    return (3 * n) - (m + 1)

def v_flip(n):
  return (lambda m: v_fl(n,m))

# There's no spec for the behavior
# of list(s) for sets s beyond
# list(s) and s having the same elements.
# So we do the dumb thing.

def remove(a,l):
  if l == []:
    return l
  elif a == l[0]:
    return l[1:]
  else:
    return l[0:1] + remove(a,l[1:])

def bag_diff(s,m):
  if m == []:
    return s
  else:
    return bag_diff(remove(m[0],s), m[1:])

def missing_below(m,l):
  ms = range(m)
  ms.reverse()
  return bag_diff(ms,l)

def act_natural (n,s,m):
  if s[0] == "Rot":
    return rot(n)(s[1])(m)
  if s[0] == "VRot":
    return v_flip(n)(rot(n)(s[1])(m))
  if s[0] == "PRot":
    return p_flip(n)(rot(n)(s[1])(m))
  if s[0] == "VPRot":
    return v_flip(n)(p_flip(n)(rot(n)(s[1])(m)))
  else:
    raise Exception

def act_face_pair (n,s,p):
  (m0,m1) = p
  a_n = act_natural
  (x,y) = (a_n (n,s,m0), a_n(n,s,m1))
  if x > y:
    return (x,y)
  else:
    return (y,x)

def act_face_pairing (n,s,l):
  l0 = map((lambda p: act_face_pair(n,s,p)),l)
  l0.sort()
  l0.reverse()
  return l0

def orbit_with_repeats(n,l):
  nms = range(n)
  nms.reverse()
  afp = act_face_pairing
  symm_types = ["Rot","VRot","PRot","VPRot"]
  out = []
  for s in symm_types:
    for t in nms:
      out = [afp(n,(s,t),l)] + out
  return out

def faces(l):
  if l == []:
    return []
  else:
    (x,y) = l[0]
    return [x,y] + faces(l[1:])

def next_face_pairs (n,l):
  mb = missing_below(2*n, faces(l))
  if mb == []:
    return nil
  else:
    M = mb[0]
    ms = mb[1:]
    return map((lambda m: (M,m)), ms)
 
def smush (r,m) :
  if m == []:
      return r
  else:
      return smush (([m[0]] + r), m[1:])

def fpp(r,m) :
  if r == []:
      return ("PTLeaf",)
  else:
      f = r[0]
      fs = r[1:]
      if fs == []:
          return ("PTLeaf",)
      else:
          f0 = fs[0]
          fs0 = fs[1:]
          return ("PTBranch",
                  (f,f0),
                  fpp (smush(fs0, m), []),
                  fpp ([f] + fs0, [f0] + m))

def prefix_tree(n):
  fs = range(2*n)
  fs.reverse()
  return fpp(fs,[])

def left_top (pt) :
  if pt[0] == "PTLeaf":
      return []
  else:
      (str, p, lt, rt) = pt
      assert str == "PTBranch"
      return [p] + left_top(lt)


def remove_complete_path(l,pt):
  if l == []:
    return pt
  p = l[0]
  ps = l[1:]
  if pt[0] == "PTLeaf":
    return ("PTLeaf",)
  (str, pp, lt, rt) = pt
  assert str == "PTBranch"
  if p != pp:
    return ("PTBranch", pp, lt, remove_complete_path(l,rt))
  ltp = remove_complete_path(ps,lt)
  if ltp[0] == "PTLeaf":
    return rt
  return ("PTBranch", pp, ltp, rt)


def pop_top_orbit (n, llnpt):
  (reps,pt) = llnpt
  if pt[0] == "PTLeaf":
    return llnpt
  lp = left_top(pt)
  lporb = orbit_with_repeats(n, lp)
  for lpo in lporb:
    pt = remove_complete_path(lpo, pt)
  return ([lp]+reps, pt)

def unfueled_reps(n, llnpt):
  (reps,pt) = llnpt
  while pt[0] != "PTLeaf":
    (reps,pt) = pop_top_orbit(n,(reps,pt))
  return reps

def orbit_reps(n):
  return unfueled_reps(n, ([],prefix_tree(n)))
