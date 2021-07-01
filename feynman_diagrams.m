(* ::Package:: *)

(*
----
This defines the rules for the scalar product and the index contraction
----
*)
SetAttributes[SP, Orderless];
sub = {SP[a__, {b_}] SP[c__, {b_}] :> SP[a, c], SP[b_, {c_}]^2 :> SP[b, b], SP[{a_},{b_}]*SP[d__,{a_}] :> SP[d,{b}]};

(*
----
This function outputs the graph in readable format, highlighting propagators P and vertices V and
setting the values of the unknowns through conservation laws.
----
*)

write[graph_,ide_List]:= Module [ {temp,nvert,indices,npt,vert,prop,propagators,momvert,momrules,vertices,
                        colIndices,lorIndices,listp,idvert,idrules,idlist,
                          rulestemp,rulesQED,rulesQCD,chargetemp,rule,loop,kl},

      Print["*************"];
      Print["grafo = ", graph];

      (*This identifies the number of external lines and vertices*)
      indices = Flatten[graph];
      npt = Max[ indices];
	nvert = Min[ indices];

      (*This generates a list of points connected to every single vertex*)
      vert = Table[Cases[graph,{x___,i,y___}->{i,x + y}],{i,nvert,-1}];

      (*One Loop*)



      (*This generates the list of all propagators*)
      listp = DeleteCases[graph,{i_,_} /; Positive[i]];
      prop = Apply[P,listp,2];

      (*This verifies that the overall charge is conserved*)
            If[chargetemp != 0,
                  Return[Print["carica non si conserva"]],
            chargetemp
            ];

      (*This is done to use the values of the input identities*)
      rule=Table[id[i]->ide[[i]],{i,1,npt}];


      (*
      This generates the pattern of the momentum linked to every line,
      using the convention that p[n] with n positive is an external leg momentum,
      p[j,m] = -p[m,j] with negative m and j is the momentum of the internal line,
      and that every line with positive p[] is incoming and every internal line is going from j to m (with j>m),
      so that the sign convention is well defined
      *)
      momvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->p[l]];
      momvert = ReplaceRepeated[momvert,{j_,m_} /; Negative[m] && m<j -> -p[j,m]];
      momvert = ReplaceRepeated[momvert,{j_,m_} /; Negative[m] && j<m -> p[m,j]];

      (*One Loop on one line vertice 4*)
      momvert = ReplaceRepeated[momvert,{j_,m_} /; j==m -> k[m]];
      momvert= ReplaceAll[ momvert, {x___,k[z_],y___}->{x, -k[z], k[z], y}];

      Print["momvert ",momvert];

      (*one loop on one line vertice 3*)
      momvert= ReplaceAll[ momvert, {x___,l_.*p[z_,w_],y___,l_.*p[z_,w_],q___}->{x, -l*k[z], y,l*p[z,w],q}];

      (*one general loop*)
      loop = graph;
      While[Cases[loop, {x_, y_} /; Count[loop, x, 2] < 2 || Count[loop, y, 2] < 2] =!= {}, (*This finds the loop*) 
            loop = DeleteCases[loop, {x_, y_} /; Count[loop, x, 2] < 2 || Count[loop, y, 2] < 2]
      ];

      If[loop =!= {} && loop =!= {{-1,-2},{-1,-2}}, (*it was ContainsNone[loop,{{-1,-2}}]*) (*serve sistemarlo per g4*)
            Print[loop];
            kl = loop[[1]] /. {l_,s_} -> p[l,s];
            momvert = momvert /. kl -> -k,
            loop  
      ];

      (*Print[momvert];*)

      (*
      This generates the list of particle identities
      *) 
      idvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->id[l]] /. rule;
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && m<j -> -id[j,m]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && j<m -> id[m,j]];

      (*Print["....",idvert];*)
 

      (*One Loop on one line*)
      idvert = ReplaceAll[ idvert, {x___,{z_,z_},y___}->{x, -id[z,z], id[z,z], y}]; (*va sistemato tutto dopo prima per gestire una lista...*)
      idvert = ReplaceAll[ idvert, {x___, p_.*id[z_,w_], v___, p_.*id[z_,w_], y___}->{x, p*id[w,z], v, -p*id[z,w], y}];

      Print["*** " , idvert];

      (*ad albero è più facile determinarli precisi, a loop meglio generare tutti e escludere poi*)
      If[loop === {},
      idlist = identity[idvert],
      idlist = identityOneLoop[idvert]
      ];

      (*When the function returns Null, it is because there is an unphysical vertex, furthermore I have to exclude the others*)
      If[idlist===Null || ContainsAny[{{0,0,0},{0,0,0,0}},idlist] || Apply[Plus,idlist,2] =!= Table[0,{i,1,Length[idlist]}],
      
            Print["Impossibile procedere! Vertici non fisici!"];

            Return[0];

      ];


      (*Lorentz indices*)
      lorIndices = ReplaceAll[vert,{o_,s_} /; Negative[o] -> mi[s]];


      (*Colour Indices*)
      colIndices = ReplaceAll[vert,{o_,s_} /; Negative[o] -> col[s]];

      (*These are the rules of momentum conservation throughout the graph*)
      momrules = momentum[momvert,nvert,npt];

      Print["momrules ", momrules];


      (*DA QUI DEVE PARTIRE IL MEGA MAPPPPPPP o sotto? stare attento che visogna passare tutto il necessario al map
      , se posso far calcolare delle cose tipo i momenti suito qui, per non generare delle copie van fatte prima del map ricordati*)

      Print["idlist su cui fare il map ", idlist];

      If[loop === {},
            Return[amplitude[idlist,vert,nvert,momvert, lorIndices,colIndices,idvert,prop,listp,momrules]], 
            Return[amplitude[#,vert,nvert,momvert, lorIndices,colIndices,idvert,prop,listp,momrules]&/@idlist]
      ];

];

amplitude[idlist_,vert_,nvert_,momvert_, lorIndices_,colIndices_,idvert_,prop_,listp_,momrules_] := 
            Module[ {vertices,idrules,propagators,rulestemp,temp,rulesQED},


      (* 
      This generates a table relative to a single vertex (3 or 4 incoming lines), 
      containing the useful information for every incoming/outgoing line in that vertex,
      i. e. momentum, charge, lorenz index and color
      *)
            vertices = Table[
            
                              If[Length[vert[[i]]]==3,
                                    Apply[V3[i],
                                          {momvert[[i]],idlist[[i]],lorIndices[[i]],colIndices[[i]]}],
            
                                    Apply[V4[i],
                                          {momvert[[i]],idlist[[i]],lorIndices[[i]],colIndices[[i]]}]]      
            
                        ,{i,nvert,-1}];


      idrules = identityrules[idvert,idlist];

      
      propagators = Table[
                  
            Apply[prop[[i]],{Apply[p,listp[[i]]],Apply[id,listp[[i]]],Map[mi,listp[[i]]],Map[col,listp[[i]]]}]
            
      ,{i,1,Length[listp]}];
      
      rulestemp = Flatten[Join[momrules,idrules]];   
          
      temp = Flatten[Join[vertices,propagators] /.rulestemp];


      Print["espressione = ",temp];

      rulesQED = {V3[_][args__] -> vertex3scalarQED[args],V4[_][args__] -> vertex4scalarQED[args],P[__][args__] -> propagatorscalarQED[args]};

      temp=temp /.rulesQED;

      temp = Apply[Times,temp];

      Print ["M = ",temp //. sub];

      temp //. sub


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
*-1 stays for electron
*1 for positron
*0 for photon,
that all external lines identities are known and the flow convention is all incoming and the internal lines go from m to l with m>l.
----
*)

identity[idvert_] := 

      If[Cases [idvert, {___,_.*id[_,_],___}] =!= {}, (*identifies if there are still unknown values*)


            id3vert = Cases [idvert, {___,_.*id[_,_],___}]; (*identifies the list of unknown values*)

            id3verttemp = DeleteCases [id3vert, {_,_,_,_} | {___,_.*id[_,_],___,_.*id[_,_],___} | {_.*id[_,_],_.*id[_,_],_.*id[_,_]}];
            (*identifies if the unknown list is a three vertex list, the first one to be elaborated*)

            If[id3verttemp==={}, (*if there are no three vertex unknown proceed with the four vertex*)

                  (*
                  **** FOUR LINE VERTEX ****
                  *)
                  
                  id4verttemp = DeleteCases [id3vert, {___,_.*id[_,_],___,_.*id[_,_],___} | {_.*id[_,_],_.*id[_,_],_.*id[_,_]}];
                  (*identifies the four vertex list with just one unknown for every vertex*)

                  If[id4verttemp =!= {}, (*Proceeds if there are unambiguosly known vertices*)

                        knowns = DeleteCases [id4verttemp, _.*id[_,_],2];

                        (*This checks if there are unphysical vertices, otherwise it breaks and returns to main*)
                        Which[Cases[knowns,{0,0,0}]=!={},
                  
                                    Return[Print["vertice a 4 con tre fotoni!"]],

                              Cases[knowns,{-1,-1,-1}]=!={},
                  
                                    Return[Print["vertice a 4 con tre elettroni!"]],

                              Cases[knowns,{1,1,1}]=!={},
                  
                                    Return[Print["vertice a 4 con tre positroni!"]]

                        ];

                        unknowns = DeleteCases [id4verttemp, 1 | 0 | -1 ,2];
                  
                        (*This solves the vertex system through charge conservation in every vertex*)
                        rules4vert = DeleteDuplicates[Table[

                              Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*(-1)*Apply[Plus,knowns[[i]]]

                        ,{i,1,Length[id4verttemp]}] /. _.*id[j_,k_]->id[j,k]]; (*this rule resets the l factor in the rule*)

                        idverttemp = idvert /. rules4vert;
                  
                        (*This iterates the process to solve all verices*)
                        identity[idverttemp],

                        (*ELSE: id4verttemp is empty, so there are more options*)

                        Print["ambiguit\[AGrave]"] 

                        (*NOTA: per avere un vertice come lambda*phi^4 (e-e+->e-e+, 
                        genero lista mettendo una graffa extra come nel solve[] e poi su identity, qui nel vertice a 4 metto map[identity,idverttemp])*)
                  
                        (*succede solo nel vertice a 4 credo, si risolve con il doppio {{opz1},{opz2}} e poi il map*)

                  ],

                  (*If the list of three verices was not empty, it uses the same mathod as above for a three line vertex*)

                  (*
                  **** THREE LINE VERTEX ****
                  *)

                  knowns = DeleteCases [id3verttemp, _.*id[_,_],2];

                  (*Checks for unphysical vertices*)
                  Which[Cases[knowns,{0,0}]=!={},
                  
                        Return[Print["vertice a 3 con due fotoni!"]],

                        Cases[knowns,{-1,-1}]=!={},

                        Return[Print["vertice a 3 con due e-!Forse 2*e- vertex!"]],

                        Cases[knowns,{1,1}]=!={},

                        Return[Print["vertice a 3 con due e+!Forse 2*e+ vertex!"]]

                  ];

                  unknowns = DeleteCases [id3verttemp, 1 | 0 | -1 ,2];

                  rules3vert = DeleteDuplicates [Table[

                        Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*(-1)*Apply[Plus,knowns[[i]]]

                  ,{i,1,Length[id3verttemp]}] /._.*id[j_,k_]->id[j,k]];

                  idverttemp = idvert /. rules3vert;

                  identity[idverttemp]

                  
            ],

            (*when the unknown list is empty it resturns the overall list of all values*) 
            idvert

]; 

identityOneLoop[idvert_] := Module [ {pos,n,vert,templist,temp,tempino}, (*questo metodo fallirebbe miseramente se avessi più di un loop*)

      (*loop non serve*)
      Print["i'm in identity one loop"];

      templist = recursion[idvert];
      Print["... 2 print ",templist];

      temp = templist /. {___,{___,l_.*id[x_,y_],___},___} -> l*id[x,y];

      While[ MatchQ[temp,templist] =!= True,
      templist = Flatten[Map[recursion,templist],1];
      (*Print["lista a multilivelli", templist];*)
      temp = templist /. {___,{___,l_.*id[x_,y_],___},___} -> l*id[x,y];
      (*Print["********************** ",MatchQ[temp,templist]];*)
      ];
      
      (*Print["lista a multilivelli", templist];*)
      Print["quante comb ", Length[templist]];
(*
      Print["Check su quante sono buone"];*)

      n = Length[idvert];

      (*Print["firstly " , Apply[Plus,templist,{2}]];*)

      tempino = Table[0,{i,1,n}];

      pos = Position[Apply[Plus,templist,{2}],tempino];

      (*Print[tempino];*)

      Print[pos];

      templist = Extract[templist,pos];

      Print[templist];

      templist = DeleteCases[templist, {___,{0,0,0},___} | {___,{0,0,0,0},___} , 2];

      Print[templist]; 

      If[templist==={}, 
            Return[Print["nessuna combinazione possibile!"]],
            templist
            ];

      templist


      (*NOTA: Potrebbero esserci altri check, controlla tutto, inoltre devi restituire templist,
      inoltre nel main se la lista ritorna vuota, manda in vertici non fisici immediatamente, se no devo mettere if {} return [0], qui direttamente*)

];

recursion[idvert_] := Module[ {temp}, (*credo non funzioni con g2 e g1...*)

      (*Print["sto agendo su", idvert];*)
      temp = idvert /. {___,{___,_.*id[x_,y_],___},___} -> id[x,y]; (*giusto scritto così? prefatt non necessario per simm 1,-1*)
      (*Print["temp ",temp];*)

      templist = idvert /. {{temp -> 0}, {temp -> 1}, {temp -> -1}};
      (*Print["... 1 print ",templist];*)

      templist
];


(*
----
This function generates the list of transformation rules used for the particles' identity within the propagators
---- 
*)
identityrules [unknowns_, knowns_] := Module[ {pos},

      pos = Position[unknowns,id[_,_],2]; (*under level two it sets the unknown position to -id[_,_]*)

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
propagatorscalarQED[p_,id_,mi_List,col_List] :=

      If[ id=== 0, (*if the propagator is a photon*)

            I*SP[{mi[[1]]},{mi[[2]]}]/p^2,

            (*if the propagator is either a p or an e*)

            I/(p^2-m^2)

      ];


vertex3scalarQED[q_List, id_List, mi_List, col_List] := Module [ {posf,pose, posp},

      posf = Flatten[Position[id,0]];
      pose = Flatten[Position[id,-1]];
      posp = Flatten[Position[id,1]];


      (*Which[pose==={}, (*I have two positrons*)

            I*qe*SP[Part[q,posp[[1]]]+Part[q,posp[[2]]],{Part[mi,posf[[1]]]}],

            posp==={}, (*I have two electrons*)

            I*qe*SP[-Part[q,pose[[1]]]-Part[q,pose[[2]]],{Part[mi,posf[[1]]]}],

            pose=!={} && posp=!={}, (*I have both a positron and an electron*)

            I*qe*SP[-Part[q,pose[[1]]]+Part[q,posp[[1]]],{Part[mi,posf[[1]]]}]

      ]*)

      I*qe*SP[-Part[q,pose[[1]]]+Part[q,posp[[1]]],{Part[mi,posf[[1]]]}] (*Dove i più e dove i meno? dovrebbe bastar solo questo..*)

];


vertex4scalarQED[q_List, id_List, mi_List, col_List] := Module [ {posf},


      posf = Position[id,0]; (*identifies the position of the two photons in the list arguments*)

      If[posf === {},

      I*lambda,

      2*I*qe^2*SP[{Part[mi,posf[[1]][[1]]]},{Part[mi,posf[[2]][[1]]]}]

      ]


];

Squaredamplitude[graph_List, iden_List] := Module[ {temp,ma,n},

      n = Length[iden];

      Print["identities = ", iden];

      posf = Position[iden,0];
      pose = Position[iden,1];

      ma = write[#,iden]&/@graph;

      ma = ma * SP[{mi[posf[[2]][[1]]]},epsilon[posf[[2]][[1]]]]*SP[{mi[posf[[1]][[1]]]},epsilon[posf[[1]][[1]]]];

      ma

];