import n as n
import a as a

from numpy.testing import assert_allclose

assert (a.hidden_weights==n.hidden_weights).all()
assert_allclose(n.hidden_bias.reshape(2),a.hidden_bias,rtol=1e-15,strict=True)
assert n.output_bias[0][0]==a.output_bias
assert (a.output_weights==n.output_weights.reshape(2)).all()
