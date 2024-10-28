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
    assert_allclose(bs@cs,m(bs,cs),rtol=1e-10,strict=True)

    ds=np.random.rand(K,N)
    mT=apple.jit(f"[(x::Arr ({M}×{N}) float)%.|:(y::Arr ({K}×{N}) float)]")
    assert_allclose(bs@ds.T,mT(bs,ds),rtol=1e-10,strict=True)

test(4,512,8);test(2,100,16)
test(10000,784,128)
test(64,5,64); test(100,2,15)
test(257,32,32);test(3,3,3)
