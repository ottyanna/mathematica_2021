(* ::Package:: *)

SetAttributes[SP, {Orderless}];
sub = {SP[a__, {b_}] SP[c__, {b_}] :> SP[a, c], SP[b_, {c_}]^2 :> SP[b, b], SP[{a_},{b_}]*SP[d__,{a_}] :> SP[d,{b}]};

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
      
            Print["Impossibile procedere"];

            Return[0];

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

      Print["*************"];

      Print[vertices];

      (*Print[idvert];
      Print[idlist];*)

      idrules = identityrules[idvert,idlist];

      Print[idrules];


      
      propagators = Table[
                  
            Apply[prop[[i]],{Apply[p,listp[[i]]],Apply[id,listp[[i]]],Apply[Q,listp[[i]]],Map[mi,listp[[i]]],Map[col,listp[[i]]]}]
            
      ,{i,1,Length[listp]}];
            

      (*Print[vertices];*)
      (*Print[propagators];*)


      rulestemp = Flatten[Join[momrules,idrules]];

      (*vertices = vertices //. _.*p[a_,b_]-> -p[a,b];*) (*non mi piace molto questa soluzione...*)

      temp = Flatten[Join[vertices,propagators] /.rulestemp];


      (*Print[temp];*)

      rulesQED = {V3[_][args__] -> vertex3scalarQED[args],V4[_][args__] -> vertex4scalarQED[args],P[__][args__] -> propagatorscalarQED[args]};

      (*Print[rules];*)

      (*Print[rulesQED];*)

      temp=temp /.rulesQED;

      Print[temp];

      (*sub = {SP[a__, {b_}] SP[c__, {b_}] -> SP[a, c], SP[b_, {c_}]^2 -> SP[b, b], SP[{a_},{b_}]*SP[d__,{a_}] -> SP[d,{b}]};*)

      temptemp = Apply[Times,temp];

      (*Print[temptemp //. sub];*)

      temptemp //. sub

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
                        Which[Cases[knowns,{0,0,0}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]],

                              Cases[knowns,{-1,-1,-1}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]],

                              Cases[knowns,{1,1,1}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]]

                        ];

                        unknowns = DeleteCases [id4verttemp, 1 | 0 | -1 ,2];

                  (*Print[knowns];
                  Print[unknowns];*)
                  
                        (*This solves the vertex system*)
                        rules4vert = Table[

                              Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*(-1)*Apply[Plus,knowns[[i]]]

                              (*Which[
                                    
                                    Sort[knowns[[i]]]==={-1,0,1} || Sort[knowns[[i]]] === {0,1,1} || Sort[knowns[[i]]] === {-1,-1,0} ,
                                    (*
                                    if the 4 vertex contains e,p and f (Actually an overkill, I think) or either two electrons or two positrons and a photon,
                                    it outputs a photon 
                                    *)

                                          Part[unknowns,i,1] -> 0,

                                    Sort[knowns[[i]]]==={-1,0,0},
                                    (*
                                    if the 4 vertex contains two photons and an electron, it outputs an electron
                                    *)
                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*1,

                                    Sort[knowns[[i]]]==={0,0,1},
                                    (*
                                    if the 4 vertex contains two photons and a positron, it outputs a positron
                                    *)
                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*-1,

                                    (*lambda*phi^4*)

                                    Sort[knowns[[i]]] === {-1,1,1},

                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*-1,

                                    Sort[knowns[[i]]] === {-1,-1,1},

                                          Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*1
            
                                    ]*)


                        ,{i,1,Length[id4verttemp]}] /. _.*id[j_,k_]->id[j,k]; (*this rule resets the right values following the convention*)

                  (*Print[rules4vert];*)

                        rules4vert = DeleteDuplicates[rules4vert];

                        (*These update the vertex list with the newly found values*)
                        (*idverttemp = idvert /. _.*id[j_,k_]->id[j,k];*)

                  (*Print[idverttemp];*)

                        idverttemp = idvert /. rules4vert;
                  
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

                  Which[Cases[knowns,{0,0}]=!={},
                  
                        Return[Print["vertice a 3 con due fotoni!"]],

                        Cases[knowns,{-1,-1}]=!={},

                        Return[Print["vertice a 3 con due e-!Forse 2*e- vertex!"]],

                        Cases[knowns,{1,1}]=!={},

                        Return[Print["vertice a 3 con due e+!Forse 2*e+ vertex!"]]

                  ];

                  unknowns = DeleteCases [id3verttemp, 1 | 0 | -1 ,2];

                  (*Print[id3verttemp];
                  Print[knowns];
                  Print[unknowns];*)

                  rules3vert = Table[

                        Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*(-1)*Apply[Plus,knowns[[i]]]


                        (*Which[
                  
                              ContainsOnly[knowns[[i]],{-1,1}], 
                              (*if the 3 vertex contains a positron and an electron, two electrons or two positrons
                              it outputs a photon*)

                                    Part[unknowns,i,1] -> 0,

                              ContainsOnly[knowns[[i]],{-1,0}],
                              (*if the 3 vertex contains an electron and a photon,
                              it outputs an electron*)

                                    Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*1,

                              ContainsOnly[knowns[[i]],{1,0}],
                              (*if the 3 vertex contains a positron and a photon,
                              it outputs a positron*)

                                    Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*-1
            
                        ]*)


                  ,{i,1,Length[id3verttemp]}] /._.*id[j_,k_]->id[j,k];
      
                  (*Print[rules3vert];*)

                  rules3vert= DeleteDuplicates[rules3vert];

                  Print[rules3vert];

                  Print[idvert];

                  (*idverttemp = idvert /. _.*id[j_,k_]->id[j,k];*)

                  (*idverttemp = idverttemp /. rules3vert;*)

                  (*idverttemp = idvert /. l_.*id[j_,k_]->-l*id[j,k];*)

                  (*Print[idverttemp];*)

                  idverttemp = idvert /. rules3vert;

                    Print[idverttemp];

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

      If[ id=== 0, (*if the propagator is a photon*)

            I*SP[{mi[[1]]},{mi[[2]]}]/p^2,

            (*if the propagator is a lepton*)

            I/(p^2-m^2)

      ];


vertex3scalarQED[q_List, id_List, Q_List, mi_List, col_List] := Module [ {posf,pose, posp},

      (*Print[id];*)

      posf = Flatten[Position[id,0]];
      pose = Flatten[Position[id,-1]];
      posp = Flatten[Position[id,1]];

      Print[q];

      (*Print["+++++++++++"];

      Print[posp];
      Print[pose];
      Print[posf[[1]]];*)


      Which[pose==={}, (*I have two positrons*)

            (*Print["Pose empty"];*)

            I*qe*SP[Part[q,posp[[1]]]+Part[q,posp[[2]]],{Part[mi,posf[[1]]]}],

            posp==={}, (*I have two electrons*)

            (*Print["Posp empty"];*)

            I*qe*SP[-Part[q,pose[[1]]]-Part[q,pose[[2]]],{Part[mi,posf[[1]]]}],

            pose=!={} && posp=!={}, (*I have both a positron and an electron*)

            (*Print["...."];*)

            I*qe*SP[-Part[q,pose[[1]]]+Part[q,posp[[1]]],{Part[mi,posf[[1]]]}]

      ]

];


vertex4scalarQED[q_List, id_List, Q_List, mi_List, col_List] := Module [ {posf},


      posf = Position[id,0]; (*identifies the position of the two photons in the list arguments*)

      (*Print[posf];*)

      If[posf === {},

      I*lambda,

      2*I*qe^2*SP[{Part[mi,posf[[1]][[1]]]},{Part[mi,posf[[2]][[1]]]}]

      ]


];


Wardidentity[graph_List, iden_List] := Module[ {temp,ma},


      posf = Position[iden,0];

      ma = write[#,iden]&/@graph;

      (*ma = Apply[Plus,ma];*)

      ma=-ma[[1]]+ma[[3]]+ma[[4]];

      ma = ma * SP[{mi[posf[[1]][[1]]]},p[posf[[1]][[1]]]]*SP[{mi[posf[[2]][[1]]]},p[posf[[2]][[1]]]];

      Print[ma];

      ma = Expand[ma];

      rule = { (p[a_]+p[b_])^2 -> m^2 + 2*SP[p[a],p[b]],SP[a__,v_.*p[c__]+w___]->v*SP[a,p[c]]+SP[a,w] };

      ma = ma //. rule; 

      Print[ma];

      ma = ma //. sub;

      Print[ma];

      ma = Together[ma]

      (*Collect[ma,SP[epsilon[x_],y_]]*)

];


