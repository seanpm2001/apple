import numpy as np;import apple

def vs(M,N):
    A=np.random.rand(M,N);x=np.random.rand(N)
    v=apple.jit(f"[(x::Arr ({M}×{N}) float)%:y]")
    print(A@x);print(v(A,x))

vs(100,32)
def test(M,N,K):
    bs=np.random.rand(M,N);cs=np.random.rand(N,K)
    m=apple.jit(f"[(x::Arr ({M}×{N}) float)%.(y::Arr ({N}×{K}) float)]")
    assert (bs@cs==m(bs,cs)).all()

    ds=np.random.rand(K,N)
    mT=apple.jit(f"[(x::Arr ({M}×{N}) float)%.|:(y::Arr ({K}×{N}) float)]")
    print(bs@ds.T);print(mT(bs,ds))

test(10000,784,128)
test(257,32,32)
