: Copyright (c) California Institute of Technology, 2006 -- All Rights Reserved
: Royalty free license granted for non-profit research and educational purposes.
ASSIGNED {
	ek        (mV)      
	celsius    (degC)
	v          (mV)
	ik        (mA/cm2)
	ninf
	ntau
}

BREAKPOINT {
	SOLVE states METHOD cnexp
	ik = gbar*(n^exp_n)*(v - ek)
}

INITIAL {

	rates(v)
	n = ninf
}
