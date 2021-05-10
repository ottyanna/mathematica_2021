(* ::Package:: *)

(*
----
Given the specific theory, this function outputs the graph in readable format, highlighting propagators P and vertices V and
setting the values of the unknowns through conservation laws.
----
*)

write[graph_]:= Module [ {temp,nvert,indices,npt,vert,prop,propagators,momvert,momrules,vertices,
                                    colIndices,lorIndices,listp,qvert,qverttemp,idvert,idrules,idlist},

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



      (*Sbagliati tutti i segni*)
      qvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->Q[l]];
      (*Q[1]=0;
      Q[2]=-1;*)
      (*qverttemp = ReplaceRepeated[qvert,{j_,m_} /; Negative[m] && m<j -> +Q[j,m]];
      qverttemp = ReplaceRepeated[qverttemp,{j_,m_} /; Negative[m] && j<m -> -Q[m,j]];*)
      qvert = ReplaceRepeated[qvert,{j_,m_} /; Negative[m] && j<m -> Q[m,j]];
      qvert = ReplaceRepeated[qvert,{j_,m_} /; Negative[m] && m<j -> Q[j,m]];

      idvert = ReplaceAll[vert,{k_,l_} /; Positive[l]->id[l]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && j<m -> id[m,j]];
      idvert = ReplaceRepeated[idvert,{j_,m_} /; Negative[m] && m<j -> id[j,m]];

      idlist = identity[idvert,nvert,npt];

      Print[idlist];

      (*Print[vert];*)

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


      
      propagators = Table[
                  
            Apply[prop[[i]],{Apply[p,listp[[i]]],Apply[Q,listp[[i]]],Map[mi,listp[[i]]]}]
            
      ,{i,1,Length[listp]}];
            

      (*Print[vertices];*)
      (*Print[propagators];*)

      temp = Join[vertices,propagators];

      rules = momrules;

Flatten[temp /. rules ]

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

identity[idvert_,nvert_,npt_] := 

      (*this identifies just the easy three line vertex linked to external lines *)

      If[Cases [idvert, {___,id[_,_],___}] =!= {},

      Print["________________"];

      Print[idvert];

      id3vert = Cases [idvert, {___,id[_,_],___}];

      Print[id3vert];

      id3verttemp = DeleteCases [id3vert, {_,_,_,_} | {___,id[_,_],___,id[_,_],___} | {id[_,_],id[_,_],id[_,_]}];

      knowns = DeleteCases [id3verttemp, id[_,_],2];

      unknowns = DeleteCases [id3verttemp, p | f | e ,2];

      Print[id3verttemp];
      Print[knowns];
      Print[unknowns];

      rules3vert = Table[

            Which[
                  
                  Part[knowns,i,1]===e && Part[knowns,i,2]===p || Part[knowns,i,1]===p && Part[knowns,i,2]===e ||
                  Part[knowns,i,1]===p && Part[knowns,i,2]===p || Part[knowns,i,1]===p && Part[knowns,i,2]===p,

                        Part[unknowns,i,1] -> f,

                  Part[knowns,i,1]===e && Part[knowns,i,2]===f || Part[knowns,i,1]===f && Part[knowns,i,2]===e,

                        Part[unknowns,i,1] -> e,

                  Part[knowns,i,1]===f && Part[knowns,i,2]===p || Part[knowns,i,1]===p && Part[knowns,i,2]===f,

                        Part[unknowns,i,1] -> p
            
             ]


      ,{i,1,Length[id3verttemp]}];
      
      Print[rules3vert];

      idverttemp = idvert /. rules3vert; 

      identity [idverttemp,nvert,npt],

      (*else*) idvert

      ];





(*
vertexrule[vertex_, nlines_] := Module [ {temp},

      If[n==3,

      i*gs*(g[Part[vertex,2,1],Part[vertex,2,2]]*(Part[vertex,1,1]-Part[vertex,1,2])[P])    
      
      
      
      ]





];*)
