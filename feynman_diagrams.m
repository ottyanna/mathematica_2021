(* ::Package:: *)

(*
----
This function outputs the graph in readable format, highlighting propagators P and vertices V and
setting the values of the unknowns through conservation laws.
----
*)

write[graph_]:= Module [ {temp,nvert,indices,npt,vert,prop,propagators,momvert,momrules,vertices,
                        colIndices,lorIndices,listp,qvert,qverttemp,idvert,idrules,idlist,
                          rulestemp},

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

      (*
      This generates the pattern of the momentum linked to every line,
      using the convention that p[n] with n positive is an external leg momentum,
      p[j,m] = -p[m,j] with m and j negatives is the momentum of the internal line,
      and that every line with positive p[] is incoming and every internal line is going from j to m (with j>m),
      so that the sign convention is well defined
      *)
      momvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->p[l]];
      momvert = ReplaceRepeated[momvert,{j_,m_} /; Negative[m] && m<j -> p[j,m]];
      momvert = ReplaceRepeated[momvert,{j_,m_} /; Negative[m] && j<m -> -p[m,j]];

      (*
      This generates the list of particle identities
      *) 
      idvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->id[l]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && j<m -> id[m,j]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && m<j -> id[j,m]];
 
      idlist = identity[idvert,nvert,npt];

      (*Print[idlist];*)

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

      rules = {V3[_][args__] -> vertex3scalarQED[args],V4[_][args__] -> vertex4scalarQED[args],P[__][args__] -> propagatorscalarQED[args]};

      (*Print[rules];

      Print[temp /. rules];*)

      temp /.rules

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
*e stays for electron (incoming arrow in initial state)
*p for positron (outgoing arrow in initial state)
*f for photon
and that all external lines identities are known 
----
*)
identity[idvert_,nvert_,npt_] := 

      If[Cases [idvert, {___,id[_,_],___}] =!= {}, (*identifies if there are still unknown values*)

            Print["________________"];

            Print[idvert];

            id3vert = Cases [idvert, {___,id[_,_],___}]; (*identifies the list of unknown values*)

            Print[id3vert];

            id3verttemp = DeleteCases [id3vert, {_,_,_,_} | {___,id[_,_],___,id[_,_],___} | {id[_,_],id[_,_],id[_,_]}];
            (*identifies if the unknown list is a three vertex list, the first one to be elaborated,
            also ignoring the case with two or more unknowns for vertex*)

            If[id3verttemp=={}, (*if there are no three vertex unknown proceed with the four vertex*)

                  Print["________VERTICE A 4________"];
                  
                  id4verttemp = DeleteCases [id3vert, {___,id[_,_],___,id[_,_],___} | {id[_,_],id[_,_],id[_,_]}];
                  (*identifies the four vertex list with just one unknown for every vertex*)

                  knowns = DeleteCases [id4verttemp, id[_,_],2];

                  unknowns = DeleteCases [id4verttemp, p | f | e ,2];

                  Print[knowns];
                  Print[unknowns];
                  
                  (*This solves the vertex system*)
                  rules4vert = Table[

                        Which[
                                    
                              ContainsAll[knowns[[i]],{e,p,f}] || Sort[knowns[[i]]] === {f,p,p} || Sort[knowns[[i]]] === {e,e,f} ,
                              (*
                              if the 4 vertex contains e,p and f (Actually an overkill, I think) or either two electrons or two positrons and a photon,
                              it outputs a photon 
                              *)

                                    Part[unknowns,i,1] -> f,

                              Sort[knowns[[i]]]==={e,f,f},
                              (*
                              if the 4 vertex contains two photons and an electron, it outputs an electron
                              *)
                                    Part[unknowns,i,1] -> e,

                              Sort[knowns[[i]]]==={f,f,p},
                              (*
                              if the 4 vertex contains two photons and a positron, it outputs a positron
                              *)
                                    Part[unknowns,i,1] -> p
            
                                    ]


                  ,{i,1,Length[id4verttemp]}];

                  Print[rules4vert];

                  (*This updates the vertex list with the newly found values*)
                  idverttemp = idvert /. rules4vert; 
                  
                  (*If there were cases with more than one unknown this iterates the process*)
                  identity [idverttemp,nvert,npt],

                  (*If the list of three verices was not empty, it uses the same mathod as above for a three line vertex*)

                  Print["________VERTICE A 3________"];

                  knowns = DeleteCases [id3verttemp, id[_,_],2];

                  unknowns = DeleteCases [id3verttemp, p | f | e ,2];

                  Print[id3verttemp];
                  Print[knowns];
                  Print[unknowns];

                  rules3vert = Table[

                        Which[
                  
                              ContainsOnly[knowns[[i]],{e,p}], 
                              (*if the 3 vertex contains a positron and an electron, two electrons or two positrons
                              it outputs a photon*)

                                    Part[unknowns,i,1] -> f,

                              ContainsOnly[knowns[[i]],{e,f}],
                              (*if the 3 vertex contains an electron and a photon,
                              it outputs an electron*)

                                    Part[unknowns,i,1] -> e,

                              ContainsOnly[knowns[[i]],{p,f}],
                              (*if the 3 vertex contains a positron and a photon,
                              it outputs a positron*)

                                    Part[unknowns,i,1] -> p
            
                        ]


                  ,{i,1,Length[id3verttemp]}];
      
                  Print[rules3vert];

                  idverttemp = idvert /. rules3vert; 

                  identity [idverttemp,nvert,npt]

                  
            ],

            (*when the unknown list is empty it resturns the overall list of all values*) 
            idvert

      ];

(*
----
This function generates the list of transformation rules used for the particles' identity within the propagators
---- 
*)
identityrules [unknowns_, knowns_] := Module[ {pos},

      pos = Position[unknowns,id[_,_]];

      rules = DeleteDuplicates [Table[

            Part[unknowns,pos[[i]][[1]],pos[[i]][[2]]] -> Part[knowns,pos[[i]][[1]],pos[[i]][[2]]]


                              ,{i,1,Length[pos]}] ];

rules
];



propagatorscalarQED[p_,id_,Q_,mi_List,col_List] :=

      If[ id=== f,

            (*Print("22222222");*)

            I*SP[mi]/p^2,

            i/(p^2-m^2)

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


      Which[pose==={},

            (*Print["Pose empty"];*)

            I*qe*(Part[q,posp[[1]]]+Part[q,posp[[2]]])[Part[mi,posf[[1]]]],

            posp==={},

            (*Print["Posp empty"];*)

            I*qe*(-Part[q,pose[[1]]]-Part[q,pose[[2]]])[Part[mi,posf[[1]]]],

            pose=!={} && posp=!={},

            (*Print["...."];*)

            I*qe*(-Part[q,pose[[1]]]+Part[q,posp[[1]]])[Part[mi,posf[[1]]]]

      ]

];


vertex4scalarQED[q_List, id_List, Q_List, mi_List, col_List] := Module [ {posf},


      posf = Position[id,f];

      (*Print[posf];*)


      2*I*qe^2*SP[Part[mi,posf[[1]][[1]]],Part[mi,posf[[2]][[1]]]]


];


