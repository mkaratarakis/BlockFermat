def IsLocalMinOn :=
  IsMinFilter f (𝓝[s] a) a
#align is_local_min_on IsLocalMinOn

def IsLocalMaxOn :=
  IsMaxFilter f (𝓝[s] a) a
#align is_local_max_on IsLocalMaxOn

def IsLocalExtrOn :=
  IsExtrFilter f (𝓝[s] a) a
#align is_local_extr_on IsLocalExtrOn

def IsLocalMin :=
  IsMinFilter f (𝓝 a) a
#align is_local_min IsLocalMin

def IsLocalMax :=
  IsMaxFilter f (𝓝 a) a
#align is_local_max IsLocalMax

def IsLocalExtr :=
  IsExtrFilter f (𝓝 a) a
#align is_local_extr IsLocalExtr