import numpy as np;import apple

from numpy.testing import assert_array_equal,assert_allclose
def vs(M,N):
    A=np.random.rand(M,N);x=np.random.rand(N)
    v=apple.jit(f"[(x::Arr ({M}×{N}) float)%:y]")
    assert_allclose(A@x,v(A,x),rtol=1e-15,strict=True)

vs(100,32)
def test(M,N,K):
    bs=np.random.rand(M,N);cs=np.random.rand(N,K)
    m=apple.jit(f"[(x::Arr ({M}×{N}) float)%.(y::Arr ({N}×{K}) float)]")
    assert_array_equal(bs@cs,m(bs,cs))

    ds=np.random.rand(K,N)
    mT=apple.jit(f"[(x::Arr ({M}×{N}) float)%.|:(y::Arr ({K}×{N}) float)]")
    assert_allclose(bs@ds.T,mT(bs,ds),rtol=1e-10,strict=True)

test(10000,784,128)
test(257,32,32)
