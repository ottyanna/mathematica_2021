(* ::Package:: *)

(*
----
This function outputs the graph in readable format, highlighting propagators P and vertices V and
setting the values of the unknowns through conservation laws.
----
*)

write[graph_,ide_List]:= Module [ {temp,nvert,indices,npt,vert,prop,propagators,momvert,momrules,vertices,
                        colIndices,lorIndices,listp,qvert,qverttemp,idvert,idrules,idlist,
                          rulestemp,rulesQED,rulesQCD,chargetemp,rule,temptemp},

      (*This identifies the number of external lines and vertices*)
      indices = Flatten[graph];
      npt = Max[ indices];
	nvert = Min[ indices];

      (*This generates a list of points connected to every single vertex*)
      vert = Table[Cases[graph,{x___,i,y___}->{i,x + y}],{i,nvert,-1}];

      (*This generates the list of all propagators*)
      listp = DeleteCases[graph,{i_,_} /; Positive[i]];
      prop = Apply[P,listp,2];

      (*Print[listp];
      Print[prop];*)

      (*This verifies that the overall charge is conserved*)
      chargetemp = Apply[Plus,ide /. {p->1,e->-1,f->0}];
      (*Print[chargetemp];*)
            If[chargetemp != 0,
                  Return[Print["carica non si conserva"]],
            chargetemp
            ];

      (*Print["lista in input ",ide];*)

      (*This is done to use the values of the input identities*)
      rule=Table[id[i]->ide[[i]],{i,1,npt}];

      (*Print["rule =",rule];*)


      (*
      This generates the pattern of the momentum linked to every line,
      using the convention that p[n] with n positive is an external leg momentum,
      p[j,m] = -p[m,j] with m and j negatives is the momentum of the internal line,
      and that every line with positive p[] is incoming and every internal line is going from j to m (with j>m),
      so that the sign convention is well defined
      *)
      momvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->p[l]];
      momvert = ReplaceRepeated[momvert,{j_,m_} /; Negative[m] && m<j -> -p[j,m]];
      momvert = ReplaceRepeated[momvert,{j_,m_} /; Negative[m] && j<m -> p[m,j]];

      (*
      This generates the list of particle identities
      *) 
      idvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->id[l]] /. rule;
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && j<m -> id[m,j]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && m<j -> -id[j,m]];
 
      idlist = identity[idvert];


      (*When the function returns Null, it is beacuse there is an unphysical vertex*)
      If[idlist===Null,
      
            Return[Print["Impossibile procedere"]]

      ];

      (*Print["idlist ",idlist];
      Print["idlist ",DeleteDuplicates[Flatten[idlist,1]]];*)
      (*questo flatten dipende da quanti cicli fa*)

      (*charge list*)
      qvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->Q[l]];
      qvert = ReplaceRepeated[qvert,{j_,m_} /; Negative[m] && j<m -> Q[m,j]];
      qvert = ReplaceRepeated[qvert,{j_,m_} /; Negative[m] && m<j -> Q[j,m]];

      (*Lorentz indices*)
      lorIndices = ReplaceAll[vert,{o_,s_} /; Negative[o] -> mi[s]];

      (*Print[lorIndices];*)

      (*Colour Indices*)
      colIndices = ReplaceAll[vert,{o_,s_} /; Negative[o] -> col[s]];

      (* 
      This generates a table relative to a single vertex (3 or 4 incoming lines), 
      containing the useful information for every incoming/outgoing line in that vertex,
      i. e. momentum, charge, lorenz index and color
      *)
            vertices = Table[
            
                              If[Length[vert[[i]]]==3,
                                    Apply[V3[i],
                                          {momvert[[i]],idlist[[i]],qvert[[i]],lorIndices[[i]],colIndices[[i]]}],
            
                                    Apply[V4[i],
                                          {momvert[[i]],idlist[[i]],qvert[[i]],lorIndices[[i]],colIndices[[i]]}]]      
            
                        ,{i,nvert,-1}];

      (*These are the rules of momentum conservation throughout the graph*)
      momrules = momentum[momvert,nvert,npt];

      (*Print["*************"];

      Print[idvert];
      Print[idlist];*)

      idrules = identityrules[idvert,idlist];

      (*Print[idrules];*)


      
      propagators = Table[
                  
            Apply[prop[[i]],{Apply[p,listp[[i]]],Apply[id,listp[[i]]],Apply[Q,listp[[i]]],Map[mi,listp[[i]]],Map[col,listp[[i]]]}]
            
      ,{i,1,Length[listp]}];
            

      (*Print[vertices];*)
      (*Print[propagators];*)


      rulestemp = Flatten[Join[momrules,idrules]];

      temp = Flatten[Join[vertices,propagators] /.rulestemp];


      (*Print[temp];*)

      rulesQED = {V3[_][args__] -> vertex3scalarQED[args],V4[_][args__] -> vertex4scalarQED[args],P[__][args__] -> propagatorscalarQED[args]};

      (*Print[rules];*)

      (*Print[rulesQED];*)

      temp=temp /.rulesQED;

      Print[temp];

      temptemp=cont[temp];

      temptemp

      (*temp /.rulesQED*)

];

(*
----
This function prescribes the global momentum conservation
as well as the momentum conservation in every vertex
----
*)

momentum[momvert_,nvert_,npt_]:= Module [ {temp,unknowns,eqs,globcons,rules},

      unknowns = Cases[momvert,p[l_,n_]->p[l,n],2];

      globcons = {p[npt] -> Sum[-p[i],{i,1,npt-1}]};

      eqs = DeleteDuplicates[ Table[Part[Apply[Plus,momvert,{1}],i]==0,{i,1,-nvert}] /. globcons];

      rules=Solve[eqs,unknowns];

      rules

];


(*
----
This function identifies the identity of all particles, regarding the direction of the arrow,
recalling that:
*e stays for electron
*p for positron
*f for photon,
that all external lines identities are known and the flow convention is all incoming and the internal lines go from -m to -l with m<l,
so that the identity is always found in the m vertex.
----
*)

identity[idvert_] := 

      If[Cases [idvert, {___,_.*id[_,_],___}] =!= {}, (*identifies if there are still unknown values*)

            (*Print["________________"];

            Print[idvert];*)

            id3vert = Cases [idvert, {___,_.*id[_,_],___}]; (*identifies the list of unknown values*)

            (*Print[id3vert];*)

            id3verttemp = DeleteCases [id3vert, {_,_,_,_} | {___,_.*id[_,_],___,_.*id[_,_],___} | {_.*id[_,_],_.*id[_,_],_.*id[_,_]}];
            (*identifies if the unknown list is a three vertex list, the first one to be elaborated,
            also ignoring the case with two or more unknowns for vertex*)

            If[id3verttemp==={}, (*if there are no three vertex unknown proceed with the four vertex*)

                  (*Print["________VERTICE A 4________"];*)
                  
                  id4verttemp = DeleteCases [id3vert, {___,_.*id[_,_],___,_.*id[_,_],___} | {_.*id[_,_],_.*id[_,_],_.*id[_,_]}];
                  (*identifies the four vertex list with just one unknown for every vertex*)

                  If[id4verttemp =!= {}, (*Proceeds if there are unambiguosly known vertices*)

                        knowns = DeleteCases [id4verttemp, _.*id[_,_],2];

                        (*This checks if there are unphysical vertices, otherwise it breaks and returns to main*)
                        Which[Cases[knowns,{f,f,f}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]],

                              Cases[knowns,{e,e,e}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]],

                              Cases[knowns,{p,p,p}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]]

                        ];

                        unknowns = DeleteCases [id4verttemp, p | f | e ,2];

                  (*Print[knowns];
                  Print[unknowns];*)
                  
                        (*This solves the vertex system*)
                        rules4vert = Table[

                              Which[
                                    
                                    Sort[knowns[[i]]]==={e,f,p} || Sort[knowns[[i]]] === {f,p,p} || Sort[knowns[[i]]] === {e,e,f} ,
                                    (*
                                    if the 4 vertex contains e,p and f (Actually an overkill, I think) or either two electrons or two positrons and a photon,
                                    it outputs a photon 
                                    *)

                                          Part[unknowns,i,1] -> f,

                                    Sort[knowns[[i]]]==={e,f,f},
                                    (*
                                    if the 4 vertex contains two photons and an electron, it outputs an electron
                                    *)
                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*e,

                                    Sort[knowns[[i]]]==={f,f,p},
                                    (*
                                    if the 4 vertex contains two photons and a positron, it outputs a positron
                                    *)
                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*p,

                                    (*lambda*phi^4*)

                                    Sort[knowns[[i]]] === {e,p,p},

                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*e,

                                    Sort[knowns[[i]]] === {e,e,p},

                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*p
            
                                    ]


                        ,{i,1,Length[id4verttemp]}] /. {-p->e,-e->p,m_.*id[j_,k_]->id[j,k]}; (*this rule resets the right values following the convention*)

                  (*Print[rules4vert];*)

                        (*These update the vertex list with the newly found values*)
                        idverttemp = idvert /. _.*id[j_,k_]->id[j,k];

                  (*Print[idverttemp];*)

                        idverttemp = idverttemp /. rules4vert;
                        (*idverttemp = idverttemp /. {-p->e,-e->p,-f->f};*) 
                  
                        (*This iterates the process to solve all verices*)
                        identity[idverttemp],

                        (*if id4verttemp is empty, so there are more options*)

                        Print["ambiguità"] 

                  (*NOTA: per avere un vertice come lambda*phi^4 (e-e+->e-e+, 
                  genero lista mettendo una graffa extra come nel solve[] e poi su identity, qui nel vertice a 4 metto map[identity,idverttemp])*)
                  
                  (*succede solo nel vertice a 4 credo, si risolve con il doppio {{opz1},{opz2}} e poi il map*)

                  ],

                  (*If the list of three verices was not empty, it uses the same mathod as above for a three line vertex*)

                  (*Print["________VERTICE A 3________"];*)

                  knowns = DeleteCases [id3verttemp, _.*id[_,_],2];

                  Which[Cases[knowns,{f,f}]=!={},
                  
                        Return[Print["vertice a 3 con due fotoni!"]],

                        Cases[knowns,{e,e}]=!={},

                        Return[Print["vertice a 3 con due e-!Forse 2*e- vertex!"]],

                        Cases[knowns,{p,p}]=!={},

                        Return[Print["vertice a 3 con due e+!Forse 2*e+ vertex!"]]

                  ];

                  unknowns = DeleteCases [id3verttemp, p | f | e ,2];

                  (*Print[id3verttemp];
                  Print[knowns];
                  Print[unknowns];*)

                  rules3vert = Table[

                        Which[
                  
                              ContainsOnly[knowns[[i]],{e,p}], 
                              (*if the 3 vertex contains a positron and an electron, two electrons or two positrons
                              it outputs a photon*)

                                    Part[unknowns,i,1] -> f,

                              ContainsOnly[knowns[[i]],{e,f}],
                              (*if the 3 vertex contains an electron and a photon,
                              it outputs an electron*)

                                    Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*e,

                              ContainsOnly[knowns[[i]],{p,f}],
                              (*if the 3 vertex contains a positron and a photon,
                              it outputs a positron*)

                                    Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*p
            
                        ]


                  ,{i,1,Length[id3verttemp]}];
      
                  (*Print[rules3vert];*)

                  rules3vert = rules3vert  /. {-p->e,-e->p,_.*id[j_,k_]->id[j,k]};

                  (*Print[rules3vert];

                  Print[idvert];*)

                  idverttemp = idvert /. _.*id[j_,k_]->id[j,k];

                  idverttemp = idverttemp /. rules3vert; 

                  (*Print[idverttemp];*)

                  (*idverttemp = idverttemp /. {-p->e,-e->p,-f->f};*)

                  (*Print[idverttemp];*)

                  identity[idverttemp]

                  
            ],

            (*Print[idvert];*)

            (*when the unknown list is empty it resturns the overall list of all values*) 
            idvert

]; 




(*
----
This function generates the list of transformation rules used for the particles' identity within the propagators
---- 
*)
identityrules [unknowns_, knowns_] := Module[ {pos},

      pos = Position[unknowns,id[_,_],2]; (*se va sotto il livello due prende la pos di -id[_,_]*)

      (*Print[pos];*)

      rules = DeleteDuplicates [Table[

            Part[unknowns,pos[[i]][[1]],pos[[i]][[2]]] -> Part[knowns,pos[[i]][[1]],pos[[i]][[2]]]

                              ,{i,1,Length[pos]}]] ;

rules
];


(*
----
These three functions generate Feynman rules for every propagator and every vertex
----
*)
propagatorscalarQED[p_,id_,Q_,mi_List,col_List] :=

      If[ id=== f, (*if the propagator is a photon*)

            I*SP[mi]/p^2,

            (*if the propagator is a lepton*)

            I/(p^2-m^2)

      ];


vertex3scalarQED[q_List, id_List, Q_List, mi_List, col_List] := Module [ {posf,pose, posp},

      (*Print[id];*)

      posf = Flatten[Position[id,f]];
      pose = Flatten[Position[id,e]];
      posp = Flatten[Position[id,p]];

      (*Print["+++++++++++"];

      Print[posp];
      Print[pose];
      Print[posf[[1]]];*)


      Which[pose==={}, (*I have two positrons*)

            (*Print["Pose empty"];*)

            I*qe*(Part[q,posp[[1]]]+Part[q,posp[[2]]])[Part[mi,posf[[1]]]],

            posp==={}, (*I have two electrons*)

            (*Print["Posp empty"];*)

            I*qe*(-Part[q,pose[[1]]]-Part[q,pose[[2]]])[Part[mi,posf[[1]]]],

            pose=!={} && posp=!={}, (*I have both a positron and an electron*)

            (*Print["...."];*)

            I*qe*(-Part[q,pose[[1]]]+Part[q,posp[[1]]])[Part[mi,posf[[1]]]]

      ]

];


vertex4scalarQED[q_List, id_List, Q_List, mi_List, col_List] := Module [ {posf},


      posf = Position[id,f]; (*identifies the position of the two photons in the list arguments*)

      (*Print[posf];*)

      If[posf === {},

      I*lambda,

      2*I*qe^2*SP[{Part[mi,posf[[1]][[1]]],Part[mi,posf[[2]][[1]]]}]

      ]


];



cont[prod_List] := Module[ {temp,mi1,mi2,mi3,mi4,prodtemp},

      mi1 = prod /. {___, I*qe*___[mi[x_]], ___} /; x<0 ->x;

      (*Print["mi1=",mi1];*)

      mi2 = prod /. {___, SP[{mi[mi1], mi[y_]}]*___, ___} | {___, SP[{mi[y_],mi[mi1]}]*___, ___} -> y;

      (*Print["mi2=",mi2];*)


      If[   mi2=!=prod, (*I have indices to saturate*)

            (*Print[prodtemp];*)

            (*Print[mi1];

            Print[mi2];*)

            (*Print[prod];*)

            prodtemp = prod /. {SP[{mi[mi1], mi[mi2]}] | SP[{mi[mi2],mi[mi1]}] -> 1, mi[mi1] -> mi[mi2]}; (*non funziona.... se tolgo mi*)

            (*Print[prodtemp];*)

            prodtemp = prodtemp /. {h___, I*qe*x___[mi[mi2]],f___, I*qe*y___[mi[mi2]],g___} -> {h,f,g,I*qe*SP[x,y]};

            (*Print[prodtemp];*)

            (*Return[prodtemp],*)

            Return[cont[prodtemp]],

            (*else continue ahead*)

            prod
            
      ];

      mi3 = prod /. {___, ___*SP[{mi[x_],_}], ___ ,SP[{mi[z_],mi[w_]}]*___,___} | {___, ___*SP[{_,mi[x_]}], ___ ,___*SP[{mi[z_],mi[w_]}],___} /; x==z || x==w ->x;

      (*Print[mi3];*)


      If[mi3 =!= prod,

            (*Print["mi3=",mi3];*)

            mi4 = prod /. {___, SP[{mi[mi3], mi[y_]}]*___, ___} | {___, SP[{mi[y_],mi[mi3]}]*___, ___} /; y<0 -> y;

            If[mi4 =!= prod,

                  (*Print["mi4=",mi4];*)

                  prodtemp = prod /. {SP[{mi[mi3], mi[mi4]}] | SP[{mi[mi4], mi[mi3]}] -> 1,mi[mi4]->mi[mi3]};

                  Return[cont[prodtemp]],

                  prod];

            mi5 = prod /. {___, SP[{mi[mi3], mi[y_]}]*___, ___} | {___, SP[{mi[y_],mi[mi3]}]*___, ___} /; y>0 -> y;

            If[mi5 =!= prod,

                  (*Print["mi5=",mi5];*)

                  prodtemp = prod /. {SP[{mi[mi3], mi[mi5]}] | SP[{mi[mi5], mi[mi3]}] -> 1, mi[mi3]->mi[mi5]};

                  Return[cont[prodtemp]],

                  prod];

            (*else continue ahead*)

            prod

      ];

      (*ovviamente sto sbagliando qualcosa, ma non so cosa, mi piace il feel della tastiera, ma devo stare attenta a non schiacciare cose a caso
      Devo riscrivere tutta questa funzione in manierqa compatta, ripensaci.
      *)

      (*Print[mi4];*)

      prod

];





