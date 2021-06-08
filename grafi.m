grafobase = { {1,-1}, {2,-1}, {3,-1} };
tadpole = {{1,-1}, {-1,-1}}

generagrafi[n_ ] := Module[ {temp},

			    i=3;
			    listagrafi = {grafobase};
			    
			    While[ i<n,
				   nuovigrafi3 = Flatten[ Map[ inserzione3, listagrafi], 1];
				   nuovigrafi4 = Flatten[ Map[ inserzione4, listagrafi], 1];
				   
				   listagrafi = Join[ nuovigrafi3, nuovigrafi4 ];
				   ++i;
				   ];

                              listagrafi
			    ];

generagrafiOneLoop[n_ ] := Module[ {temp},

			    i=1;
			    listagrafi = {tadpole};
			    
			    While[ i<n,
				   nuovigrafi3 = Flatten[ Map[ inserzione3, listagrafi], 1];
				   nuovigrafi4 = Flatten[ Map[ inserzione4, listagrafi], 1];
				   
				   listagrafi = Join[ nuovigrafi3, nuovigrafi4 ];
				   ++i;
				   ];

                              listagrafi
			    ];

inserzione3[grafo_] := Module[{temp},
			      indici = Flatten[grafo];
			      npt = Max[ indici];
			      nvert = Min[ indici];

			      nuovigrafi=Table[ inserisci3[i,npt+1,nvert-1, grafo],
						{i,1,Length[ grafo]}
						];
			      nuovigrafi
			      ];

inserisci3[pos_, ext_, int_, grafo_] := ReplacePart[ grafo,
 		           pippo[ {ext,int}, {grafo[[pos,1]],int}, {grafo[[pos,2]], int} ],
						     pos ] /. pippo->Sequence ; 


inserzione4[grafo_] := Module[{temp},

			      indici = Flatten[grafo];
			      npt = Max[ indici];
			      nvert = Min[ indici];

			      nuovigrafi=Table[ inserisci4[i,npt+1, grafo],
						{i,nvert,-1}
						];
			      nuovigrafi = DeleteCases[ nuovigrafi, {} ];
			      nuovigrafi

			      ];




inserisci4[ vertice_, ext_, grafo_] :=  If[ Count[ grafo, vertice, 2]===3,

					    Append[ grafo, {ext,vertice}],

                                            {}

					   ]


(*Map[scrittura,listagrafi]*)