(* ::Package:: *)

(*
----
These functions generate topologically different graphs with fixed number of external lines n.
They can also generate one loop graphs.
The variable Oneloop must be set to False as an input value if it is needed a tree level diagram, otherwise it must be set to True. 
----
*)

basicgraph = { {1,-1}, {2,-1}, {3,-1} };
tadpole = { {1,-1}, {-1,-1} };

graphgeneration[n_ , Oneloop_] := Module[ {temp},

			      If[Oneloop === False,
			      i=3;
			      graphlist = {basicgraph},
				(*else*)
				i=1;
			      graphlist = {tadpole}
				];

			    
			    While[ i<n,
				   newgraphs3 = Flatten[ Map[ insertion3, graphlist], 1];
				   newgraphs4 = Flatten[ Map[ insertion4, graphlist], 1];
				   
				   graphlist = Join[ newgraphs3, newgraphs4 ];
				   ++i;
				   ];

                              graphlist
			    ];

insertion3[graph_] := Module[{temp},
			      indices = Flatten[graph];
			      npt = Max[ indices];
			      nvert = Min[ indices];

			      newgraphs=Table[ insert3[i,npt+1,nvert-1, graph],
						{i,1,Length[ graph]}
						];
			      newgraphs
			      ];

insert3[pos_, ext_, int_, graph_] := ReplacePart[ graph,
 		           supp[ {ext,int}, {graph[[pos,1]],int}, {graph[[pos,2]], int} ],
						     pos ] /. supp->Sequence ; 


insertion4[graph_] := Module[{temp},

			      indices = Flatten[graph];
			      npt = Max[ indices];
			      nvert = Min[ indices];

			      newgraphs=Table[ insert4[i,npt+1, graph],
						{i,nvert,-1}
						];
			      newgraphs = DeleteCases[ newgraphs, {} ];
			      newgraphs

			      ];




insert4[ vertex_, ext_, graph_] :=  If[ Count[ graph, vertex, 2]===3,

					    Append[ graph, {ext,vertex}],

                                            {}

					   ];

(*
----
This defines the rules for the scalar product and the index contraction
----
*)
SetAttributes[SP, Orderless];
sub = {SP[a__, {b_}] SP[c__, {b_}] :> SP[a, c], SP[b_, {c_}]^2 :> SP[b, b], SP[{a_},{b_}]*SP[d__,{a_}] :> SP[d,{b}]};
(*sub1 = {SP[a___,l_.*b__+m_.*c__+k___] :> l*SP[a,b]+m*SP[a,c]+SP[a,k]};*)
sub11 = {SP[a__,b__+c__+k___] :> SP[a,b]+SP[a,c+k]};
sub12 = {SP[k__,j_*p[c_]] :> j*SP[k,p[c]]};
sub2 = {l_.*SP[a__,b_]+m_.*SP[a__,c_] :> SP[a,l*b+m*c]}

(*
----
This function prints the graph in readable format, highlighting propagators P and vertices V and
setting the values of the unknowns through conservation laws, 
then outputs all possible Feynman amplitudes for that particular graph, using Feynman rules for scalar QED plus a lambda*phi^4 interaction.
The inputs need to be in the form of one graph with n external fields (computed with graphgeneration) and a list of field identities 
in the form {charge of first field, ... ,charge of n_th field}, recalling that, conventionally, 
the complex field can have charge 1 or -1, and the electromagnetic field has charge of 0.
If the amplitude for all graphs with fixed n external fields is neeeded the totalamplitude function should be used.
----
*)

write[graph_,ide_List]:= Module [ {temp,nvert,indices,npt,vert,prop,momvert,momrules, support,
                        colIndices,lorIndices,listp,listploop12,idvert,idlist,chargetemp,rule,loop,kl,ambiguity},

      Print["*************"];
      Print["grafo = ", graph];
      Print["identità particelle = ", ide];

      (*This identifies the number of external lines and vertices*)
      indices = Flatten[graph];
      npt = Max[ indices];
	nvert = Min[ indices];

      (*checks if everything in input is ok*)
      checksonidenities[ide,npt];

      (*This generates a list of points connected to every single vertex*)
      vert = Table[Cases[graph,{x___,i,y___}->{i,x + y}],{i,nvert,-1}];
      (*to take into account that the {-1,-1} appears just once*)
      vert = ReplaceAll[vert, {k_,k_} -> supp[{k,k},{k,k}]]; 

      (*Print[vert];*)

      (*This generates the list of all propagators*)
      listp = DeleteCases[graph,{i_,_} /; Positive[i]];
      (*Print[listp];*)
      (*This line below works ONLY in one loop case, to take account for {-1,-2},{-1,-2} that would generate the "same name" line, 
      but can be actually a different field, so it needs a different name*)
      listploop12 = listp /. {u___,{x_,y_},{x_,y_},w___} -> {u,{x,y},{y,x},w};
      (*Print[listploop12];*)
      prop = Apply[P,listp,2];


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
      (*This gives a "name" to the free momentum that runs in the loop {-1,-1}*)
      momvert = ReplaceRepeated[momvert, supp[{m_,m_},{m_,m_}] -> supp[-k[m],k[m]]] /. supp->Sequence;
      (*This gives a "name" to the free momentum that runs in the loop {z_,w_},{z_,w_}, the factor l was brough by the first part*)
      momvert = ReplaceAll[ momvert, {x___,l_.*p[z_,w_],y___,l_.*p[z_,w_],q___}->{x, -l*k[z], y,l*p[z,w],q}];
      (*This gives a "name" to the free momentum that runs in one line of one general loop,
      first the loop must be identified, then one random line the first in the loop is taken to have fixed k momentum*)
      loop = graph;
      (*This finds the loop, knowing that the "numbers" in the loop appear always at least twice, so it is recursive*)
      While[Cases[loop, {x_, y_} /; Count[loop, x, 2] < 2 || Count[loop, y, 2] < 2] =!= {}, 
            loop = DeleteCases[loop, {x_, y_} /; Count[loop, x, 2] < 2 || Count[loop, y, 2] < 2]
      ];
      If[loop =!= {} && MatchQ[loop,{{u_,w_},{u_,w_}}]===False && loop =!= {{-1,-1}},
            kl = loop[[1]] /. {l_,s_}  -> p[l,s];
            momvert = momvert /. kl -> -k,
            loop  
      ];

      support = loop /. {{u_,w_},{u_,w_}} -> p[w,u];

      (*Print[support];
      Print[loop];
      Print[momvert];*)

      (*
      This generates the list of particle identities
      *) 
      idvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->id[l]] /. rule;
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && m<j -> -id[j,m]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && j<m -> id[m,j]];
      (*This gives a "name" to the identity in the loop {-1,-1}*)
      idvert = ReplaceAll[ idvert, supp[{z_,z_},{z_,z_}] ->supp[-id[z,z], id[z,z]]] /. supp -> Sequence;
      (*This corrects the sign convention in the loop {-1,-2},{-1,-2}*)
      idvert = ReplaceAll[ idvert, {x___, p_.*id[z_,w_], v___, p_.*id[z_,w_], y___}->{x, p*id[w,z], v, -p*id[z,w], y}];


      vert = vert /. supp -> Sequence;


      (*At tree level there is a high chance that the identities are generable just imposing charge conservation in every vertex,
      with loops it's much trickier, so in order not to miss combinations all combinations need to be generated*)
      If[loop === {},
            idlist = identity[idvert],
            idlist = identityOneLoop[idvert]
      ];


      (*If there is ambiguity at tree level, identity function returns 0, then I have to consider all possible combinations*)
      If[idlist === 0, 
      
            ambiguity = True;
            idlist = identityOneLoop[idvert],

            ambiguity = False
        
        ];

      (*When the function returns Null, it is because there is an unphysical vertex, 
      furthermore the function could have genereted some other vertices satisfying the charge conservation 
      but not the theory interactions, so this case is also checked*)
      If[idlist===Null || ContainsAny[{{0,0,0},{0,0,0,0}},idlist] || Apply[Plus,idlist,2] =!= Table[0,{i,1,Length[idlist]}],
      
            Print["Impossibile procedere! Vertici non inclusi nella teoria!"];

            Return[0],

            idlist

      ];


      (*Lorentz indices*)
      lorIndices = ReplaceAll[vert,{o_,s_} /; Negative[o] -> mi[s]];

      (*Colour Indices, useful for a QCD theory case*)
      colIndices = ReplaceAll[vert,{o_,s_} /; Negative[o] -> col[s]];

      (*This generates the rules of momentum conservation throughout the graph, 
      adding the usual loop cases rules for the propagator expression (recalling that the names are "specific" and there could be no ambiguity)*)
      momrules = Flatten[Join[momentum[momvert,nvert,npt],{support->-k[-1], p[-1,-1] -> k[-1], kl -> -k}]];

      (*Print[momvert];
      Print[momrules];*)


      (*If it is a tree level diagram and it is fully determined by satisfying charge conservation in every vertex,
      the amplitude can be directly computed, otherwise the function needs to be run over all possible combinations*)
      If[loop === {} && ambiguity === False ,
            Return[amplitude[idlist,vert,nvert,momvert, lorIndices,colIndices,idvert,prop,listp,listploop12,momrules]], 
            Return[amplitude[#,vert,nvert,momvert, lorIndices,colIndices,idvert,prop,listp,listploop12,momrules]&/@idlist]
      ] ;

];

amplitude[idlist_,vert_,nvert_,momvert_, lorIndices_,colIndices_,idvert_,prop_,listp_,listploop12_,momrules_] := 
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

      (*This generates the rules for internal line identities*)
      idrules = identityrules[idvert,idlist];


      (*This generates the same table for vertices in the case of propagators, PAYING ATTENTION TO THE FACT THAT........*)      
      propagators = Table[
                  
            Apply[prop[[i]],{Apply[p,listploop12[[i]]],Apply[id,listploop12[[i]]],Map[mi,listp[[i]]],Map[col,listp[[i]]]}]
            
      ,{i,1,Length[listp]}];
      
      rulestemp = Flatten[Join[momrules,idrules]];   
          
      temp = Flatten[Join[vertices,propagators] /. rulestemp];


      Print["espressione = ",temp];

      (*This applies the Feynman rules for our scalar QED*)
      rulesQED = {V3[_][args__] -> vertex3scalarQED[args],V4[_][args__] -> vertex4scalarQED[args],P[__][args__] -> propagatorscalarQED[args]};

      temp = temp /. rulesQED;

      temp = Apply[Times,temp];

      Print ["M = ",temp //. sub];

      temp //. sub


];

checksonidenities[ide_,npt_] := Module[ {chargetemp},

      (*This checks if the number of identities is the same as the external lines*)
      If[Length[ide] != npt,
            Return[Print["Il numero delle identità non corrisponde al numero di linee esterne"]],
      ide
      ];

      (*This verifies that the overall charge in list is conserved*)
      chargetemp = Apply[Plus,ide];
      If[chargetemp != 0,
            Return[Print["carica non si conserva"]],
      chargetemp
      ];

      chargetemp

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
This function identifies the identity of all fields, recalling that for every vertex the fields are incoming,
and that:
*-1 stays for field
*1 for complex conjugate field
*0 for electomagnetic field.
Furthermore the internal lines have a natural direction imposed from m to l with m>l.
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

                        Print["ambiguit\[AGrave]"];

                        Return[0]

                  ],

                  (*If the list of three verices was not empty, it uses the same method as above for a three line vertex*)

                  (*
                  **** THREE LINE VERTEX ****
                  *)

                  knowns = DeleteCases [id3verttemp, _.*id[_,_],2];

                  (*Checks for unphysical vertices*)
                  Which[Cases[knowns,{0,0}]=!={},
                  
                        Return[Print["vertice a 3 con due fotoni!"]],

                        Cases[knowns,{-1,-1}]=!={},

                        Return[Print["vertice a 3 con due e-!"]],

                        Cases[knowns,{1,1}]=!={},

                        Return[Print["vertice a 3 con due e+!"]]

                  ];

                  unknowns = DeleteCases [id3verttemp, 1 | 0 | -1 ,2];

                  rules3vert = DeleteDuplicates [Table[

                        Part[unknowns,i,1] -> (Part[unknowns,i,1] /. l_.*id[_,_]->l)*(-1)*Apply[Plus,knowns[[i]]]

                  ,{i,1,Length[id3verttemp]}] /._.*id[j_,k_]->id[j,k]];

                  idverttemp = idvert /. rules3vert;

                  identity[idverttemp]

                  
            ],

            (*when the unknown list is empty it returns the overall list of all values*) 
            idvert

]; 


(*
----
This function generates all possible combinations for the vertices, then excluding the unphyisical ones.
It is used for graphs with one loop.
----
*)

identityOneLoop[idvert_] := Module [ {pos,n,vert,templist,temp,tempino},

      templist = recursion[idvert];

      temp = templist /. {___,{___,l_.*id[x_,y_],___},___} -> l*id[x,y];

      While[ MatchQ[temp,templist] =!= True, (*if they are the same, it means there are no more unknowns*)
            templist = Flatten[Map[recursion,templist],1];
            temp = templist /. {___,{___,l_.*id[x_,y_],___},___} -> l*id[x,y];
      ];
      
      n = Length[idvert];
      tempino = Table[0,{i,1,n}];

      (*This identifies the position of the combinations that preserve the charge conservation and then extract that combinations*)
      pos = Position[Apply[Plus,templist,{2}],tempino];
      templist = Extract[templist,pos];
      (*This checks for vertices not included in the theory*)
      templist = DeleteCases[templist, {___,{0,0,0},___} | {___,{0,0,0,0},___} , 2];

      If[templist==={}, 
            Return[Print["nessuna combinazione possibile!"]],
            templist
            ];

      templist

];

(*
----
This function identifies one unknown and generates a list setting all possible values for it
---- 
*)
recursion[idvert_] := Module[ {temp}, 

      temp = idvert /. {___,{___,_.*id[x_,y_],___},___} -> id[x,y]; 

      templist = idvert /. {{temp -> 0}, {temp -> 1}, {temp -> -1}};

      templist
];


(*
----
This function generates the list of transformation rules used for the fields' identity within the propagators
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
These three functions generate Feynman rules for every propagator and every vertex.
N.B. This is possible because all lines are taken incoming for every vertex, using the right sign.
----
*)
propagatorscalarQED[p_,id_,mi_List,col_List] :=

      If[ id === 0, (*if the propagator is a photon*)

            I*SP[{mi[[1]]},{mi[[2]]}]/p^2,

            (*if the propagator is the complex scalar field*)

            I/(p^2-m^2)

      ];


vertex3scalarQED[q_List, id_List, mi_List, col_List] := Module [ {posf,pose, posp},

      posf = Flatten[Position[id,0]];
      pose = Flatten[Position[id,-1]];
      posp = Flatten[Position[id,1]];

      I*qe*SP[-Part[q,pose[[1]]]+Part[q,posp[[1]]],{Part[mi,posf[[1]]]}]

];


vertex4scalarQED[q_List, id_List, mi_List, col_List] := Module [ {posf},


      posf = Position[id,0]; (*identifies the position of the two photons in the identity list*)

      If[posf === {},

      I*lambda,

      2*I*qe^2*SP[{Part[mi,posf[[1]][[1]]]},{Part[mi,posf[[2]][[1]]]}]

      ]


];

(*
----
This function takes into account all the possible graphs, so contibutions to the Feynman amplitude, especially at tree level,
with a fixed number n of external lines.
N.B. To take into account also the loops, it would take a lot of computation time. It is obviously possible.
----
*)

totalamplitude[graph_List, iden_List] := Module[ {temp,ma,check},

      indices = Flatten[graph];
      npt = Max[indices];

      Print["identities = ", iden];

      check = checksonidenities[iden,npt];
       If[check === Null, 
            Return[0], 
            iden];

      ma = write[#,iden]&/@graph;

      ma = Apply[Plus,ma];

      Print["++++++++++++++++++++++++++++++++++++++"];

      Print["ampiezza totale con tutti i contributi ad albero:", ma];

      ma

];

(*
----
This function verifies the Ward identity at tree level with four external lines. It's still incomplete.
----
*)

WardIdentity[graph_List, iden_List, photon_] := Module[ {temp,ma,n, rules, globcons, rule},

pose = Position[iden,1 | -1];
posf = Position[iden,0];

cons4imp = Table[ SP[p[pose[[i]][[1]]],p[pose[[i]][[1]]]] -> m^2 ,{i,1,Length[pose]}];

cons4impf = Table[ SP[p[posf[[i]][[1]]],p[posf[[i]][[1]]]] -> 0 ,{i,1,Length[posf]}];

Print[cons4impf];

rules = Join[cons4imp,cons4impf];

Print[rules];

rule = {(p[a_]+p[b_])^2 -> SP[p[a],p[a]]+ SP[p[b],p[b]] + 2*SP[p[a],p[b]]};

Print[cons4imp];

If[ iden[[photon]] =!= 0,

      Return[Print["In input serve la posizione di un fotone!"]],

      ma = Expand[totalamplitude[graph,iden]*SP[{mi[photon]},p[photon]]]

];

Print[rule];

ma = ReplaceAll[ma,rule];


Print[ma];

ma = ReplaceAll[ma,rules];

Print[ma];

ma = ma //. sub;

ma = ma //. rules;

ma = Together[Simplify[ma]];

Print[ma];

globcons = {p[1] -> Sum[-p[i],{i,2,Length[iden]}]};

(*ma = ma //. globcons;*)

ma = ma //. sub11;


Print[ma];

ma = ReplaceRepeated[ma,sub12];

ma = ma //. sub12;

Print[rules];

ma = ma //. rules;

ma = ma //. globcons;

ma = ma //. sub11;

ma = ma //. sub12;

ma = ma //.rules;

ma

];

(*WardIdentity[graph_List, iden_List, photon_] := Module[ {temp,ma,n},

pose = Position[iden,1];

If[ iden[[photon]] =!= 0,

      Return[Print["In input serve la posizione di un fotone!"]],

      ma = Expand[totalamplitude[graph,iden]*SP[{mi[photon]},p[photon]]]

];

ma = ma //. sub;



ma = ma //. sub1;

rules = {SP[p[photon],p[photon]] -> 0, (p[a_]+p[b_])^2 - m^2 -> 2*SP[p[a],p[b]] };

Print[ma//.rules];

ma = Simplify[Together[ma //. rules ]];

ma = ma //. sub2;

ma


];*)


(*WardIdentity[graph_List, iden_List] := Module[ {temp,ma,n},

      n = Length[iden];

      posf = Position[iden,0];
      pose = Position[iden,1];

      ma = write[#,iden]&/@graph;

      ma = ma * SP[{mi[posf[[2]][[1]]]},epsilon[posf[[2]][[1]]]]*SP[{mi[posf[[1]][[1]]]},epsilon[posf[[1]][[1]]]];

      ma = ma //. sub;

      Print[ma];

      ma = ma /. SP[epsilon[a_],b___+_.*p[a_]+c___] -> SP[p[a],b+c];

      Print[ma];

      (*per costruzione credo sia sempre il primo a essere quello che compare nel propagatore*)

      ma = ma /. -m^2+(p[c_]+p[b_])^2 -> 2*SP[p[c],p[b]]; (*per costruzione del fatto che hp fotoni*)

      Print[ma];

      ma = ma /. SP[w_.*o_,y_.*u_] -> w*y*SP[o,u];

      Print[ma];

      ma = ma /. {l_.*SP[epsilon[n_],k___],j___,o_.*SP[epsilon[n_],epsilon[m_]]}->{l*SP[epsilon[n],k],j,o*SP[epsilon[n],p[m]]};

      Print[ma];

      ma = Apply[Plus,ma];

      Print[ma];

      ma = ma //. j_.*SP[epsilon[a_],b_]+k_.*SP[epsilon[a_],c_] -> SP[epsilon[a],j*b+k*c];
      
      ma = ma //Simplify;

      (*If[MatchQ[ma,SP[0,epsilon[a_]]]===False,
      
      ];*)

      ma



];*)