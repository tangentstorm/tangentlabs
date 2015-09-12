NB. demo of reusing viewmat window via viewmatcc

load 'viewmat'

NB. this is a workaround for a j8 bug (as of 09/12/2015)
viewmatcc =: glpaint_jgl2_@viewmatcc_jviewmat_

w_cancel =: 3 : 0
  wd 'pclose'
)

w_g_mblup =: 3 : 0
  viewmatcc (? 30 40$ 10);'g' 
)

wd 0 : 0
  pc w closeok;
  pn randmat;
  minwh 640 480;
  cc g isidraw;  rem : would be isigraph, if not for the j8 bug;
  pshow;
)

viewmatcc (i.3 4);'g'
