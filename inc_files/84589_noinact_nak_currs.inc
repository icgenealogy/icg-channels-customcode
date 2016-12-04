: Copyright (c) California Institute of Technology, 2006 -- All Rights Reserved
: Royalty free license granted for non-profit research and educational purposes.
ASSIGNED {
	i	  (mA/cm2)
	eh	  (mV)
	ek        (mV)      
	ena        (mV)     
	celsius    (degC)
	v          (mV)
	ik        (mA/cm2)
	ina        (mA/cm2)
	ninf
	ntau
}

BREAKPOINT {
	SOLVE states METHOD cnexp
	:ik = gbar*(n^exp_n)*(v - ek)
	:ina = gbar*(n^exp_n)*(v - ena)
	i = gbar*(n^exp_n)*(v-eh)
}

INITIAL {

	rates(v)
	n = ninf
}
