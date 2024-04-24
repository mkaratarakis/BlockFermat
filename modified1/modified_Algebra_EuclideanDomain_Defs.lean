def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a
#align euclidean_domain.gcd EuclideanDomain.gcd

def xgcdAux (r s t r' s' t' : R) : R × R × R :=
  if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r
#align euclidean_domain.xgcd_aux EuclideanDomain.xgcdAux

def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2
#align euclidean_domain.xgcd EuclideanDomain.xgcd

def gcdA (x y : R) : R :=
  (xgcd x y).1
#align euclidean_domain.gcd_a EuclideanDomain.gcdA

def gcdB (x y : R) : R :=
  (xgcd x y).2
#align euclidean_domain.gcd_b EuclideanDomain.gcdB

def lcm (x y : R) : R :=
  x * y / gcd x y
#align euclidean_domain.lcm EuclideanDomain.lcm