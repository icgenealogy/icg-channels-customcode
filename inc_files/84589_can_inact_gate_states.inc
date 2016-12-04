: Copyright (c) California Institute of Technology, 2006 -- All Rights Reserved
: Royalty free license granted for non-profit research and educational purposes.
UNITS {
	(mA) = (milliamp)
	(mV) = (millivolt)
}

: Initialize everything to zero - they should all be set from the
: hoc code by the "define_param" function that writes the value
: used to a parameter file (no magic numbers, anywhere...)

PARAMETER {
	vhalf_m = -14.0 (mV)
	vsteep_m = -6.5 (mV)
	tskew_m = 0.2 
	tscale_m = 5.0 (ms)
	toffset_m = 1 (ms)
	exp_m = 2

	vhalf_h = -40 (mV)
	vsteep_h = 10 (mV)
	tskew_h = 0.5 
	tscale_h = 1 (ms)
	toffset_h = 50 (ms)
	exp_h = 1

	gbar = 1.0 (mho/cm2)
	

}

STATE {	m h }

DERIVATIVE states {
	rates(v)
	m' = (minf-m)/mtau
	h' = (hinf-h)/htau
}



PROCEDURE rates(v) {

	minf = var_inf(v, vhalf_m, vsteep_m)
	hinf = var_inf(v, vhalf_h, vsteep_h)

	mtau =  var_tau(v, vhalf_m, vsteep_m, tskew_m, tscale_m, toffset_m)
	htau =  var_tau(v, vhalf_h, vsteep_h, tskew_h, tscale_h, toffset_h)

}
