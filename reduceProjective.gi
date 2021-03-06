DeclareGlobalFunction("ExtractProjectiveTorsionSubcomplex");

InstallGlobalFunction( "ExtractProjectiveTorsionSubcomplex", function(C, p)
#####################################################################
## Here, p is the prime for which to take the torsion subcomplex.  ##
## We extract the cells the stabilizer of which contains p-torsion.##
#####################################################################
local vcd, stabilizerCardinalities, celldata, data, torsionPosition,
torsionCells, numberOfTorsionCells, n, j, returnedData, warned,
groupname, admissibilityCheck, x, i, b, tmpCell, cell, boundary, groupName,
lnth, dims, Elts, Boundary, StabilizerGroups, RotSubGroups, s,k,
boundaryList, BI, SGN, LstEl, tmp, G, Stabilizer, Action, Dimension, centerSize;

    admissibilityCheck := function(celldata)
    #########################################################
    ## A cell complex is admissible in the sense of Brown, ##
    ## if each cell stabilizer fixes its cell pointwise.   ##
    ## Additionally,				       ##
    ## we gather the cardinalities of the stabilizers.     ##
    #########################################################
    local stabilizerCardinalities, G, card, n, j, R, vcd, warned;
       warned := false;
       stabilizerCardinalities := [];
       vcd := Length(celldata)-1;

       for n in [0..vcd] do
	    stabilizerCardinalities[n+1] := [];
	    for j in [1..Length(celldata[n+1])] do
	       G :=   celldata[n+1][j]!.TheMatrixStab;
	       if IsFinite(G) then
	          card := Order(G);
	          stabilizerCardinalities[n+1][j] := card;
	          ## *** Now we have to compare              *** ##
	          ## *** with the order of "TheRotSubgroup"  *** ##
	          R := celldata[n+1][j]!.TheRotSubgroup;
	          if card > Order(R) and warned = false then
		    Print("****Warning: cell complex not admissible ",
			    "in the sense of Brown!****\n",
		    " Torsion subcomplex reduction requires cell subdivision.\n");
		    warned := true;
	          fi;
	       fi;
	    od;
       od;
       return [stabilizerCardinalities, warned];
   end;

   # Case 1: the input is a group name
   if IsString(C) then
   groupName:=C;
   groupname := Filtered( C, function ( x )
            return not (x = '(' or x = ')' or x = ',' or x = '[' or x = ']');
   end );
   Read(Concatenation( 	DirectoriesPackageLibrary("HAP")[1]![1],
			"Perturbations/Gcomplexes/",groupname));
   celldata := StructuralCopy(HAP_GCOMPLEX_LIST);

   # Case 2: the input is a variable
   else
       groupName:=fail;
       celldata:=[];
       i:=0;
       while C!.dimension(i) > 0 do
           cell:=[];
           for j in [1..C!.dimension(i)] do
               if not i=0 then
               boundary:=C!.boundary(i,j);
               Add(cell,rec(TheMatrixStab :=C!.stabilizer(i,j),
                           TheRotSubgroup:=C!.stabilizer(i,j),
                           BoundaryImage :=rec(
                                 ListIFace:=List(boundary,w->AbsInt(w[1])),
                                 ListSign:=List(boundary,w->SignInt(w[1])),
                                 ListElt:=List(boundary,w->C!.elts[w[2]])
                           )
                       )
               );
               else
               Add(cell,rec(TheMatrixStab :=C!.stabilizer(i,j),
                           TheRotSubgroup:=C!.stabilizer(i,j),
                           BoundaryImage :=rec(
                                 ListIFace:=[],
                                 ListSign:=[],
                                 ListElt:=[]
                           )
                       )
               );
               fi;
           od;
           Add(celldata,cell);
           i:=i+1;
       od;
   fi;
   vcd := Length(celldata) -1;
   centerSize:=Size(Intersection(List([1..Length(celldata[vcd+1])],i->celldata[vcd+1][i].TheMatrixStab)));
   trivialTorsion:=Lcm(centerSize,p);

#   Print("Extracting the ",p,"-torsion subcomplex of the ",
#		vcd,"-dimensional ",groupName,"-cell complex ... \n");
   returnedData := admissibilityCheck(celldata);
   stabilizerCardinalities := returnedData[1];
   warned := returnedData[2];
   torsionCells := [];
   numberOfTorsionCells := [];
   for n in [0..vcd] do
	torsionCells[n+1] := [];
	numberOfTorsionCells[n+1] := 0;
	for j in [1..Length(celldata[n+1])] do
	   ## Check if the stabilizer contains p-torsion ##
	   if (stabilizerCardinalities[n+1][j]/trivialTorsion) mod p = 0 then
#		Print("Extracted ",n,"-cell numero ",j,
#			" of stabilizer cardinality ",
#			stabilizerCardinalities[n+1][j],".\n");
		numberOfTorsionCells[n+1]
			:= numberOfTorsionCells[n+1]+1;
	        torsionCells[n+1][numberOfTorsionCells[n+1]]
			:=[n, j];
	   fi;
	od;
   od;
#   return
#     [torsionCells, numberOfTorsionCells, celldata, stabilizerCardinalities, warned];
  data:=[];
  for i in [1..Length(torsionCells)] do
      data[i]:=[];
      for x in torsionCells[i] do
          Add(data[i],celldata[i][x[2]]);
      od;
  od;
for j in [2..Size(data)] do
  for i in [1..Size(data[j])] do
      tmpCell:=StructuralCopy(data[j][i]!.BoundaryImage);
      b:=List(tmpCell!.ListIFace,w->Position(torsionCells[j-1], [j-2,w]));
      tmpCell!.ListIFace:=b;
      data[j][i]!.BoundaryImage:=tmpCell;
  od;
od;
  torsionPosition:=torsionCells;
  torsionCells:=[];
  for i in [1..Size(data)] do
     torsionCells[i]:=[];
     for j in [1..Size(data[i])] do
         torsionCells[i][j]:=[i-1,j];
     od;
  od;
  ############################
  ############Taken from dutour.gi implemented by Graham Ellis#########
  lnth:=Length(data)-1;

  dims:=List([1..lnth+1],n->Length(data[n]));

  ###################
  Dimension:=function(n);
  if n>lnth then return 0; fi;
  return dims[n+1];
  end;
  ###################

  Elts:=[Identity(data[1][1].TheMatrixStab)];
  StabilizerGroups:=[];
  RotSubGroups:=[];
  boundaryList:=[];


  #######
  for n in [1..lnth+1] do
  boundaryList[n]:=[];
  StabilizerGroups[n]:=[];
  RotSubGroups[n]:=[];
    for k in [1..Dimension(n-1)] do
    #if not name in InfGrps then
    Append(Elts,Elements(data[n][k].TheMatrixStab));
    #fi;
    Add(StabilizerGroups[n],data[n][k].TheMatrixStab);
    Add(RotSubGroups[n],data[n][k].TheRotSubgroup);
    od;
  od;
  ####

  Elts:=SSortedList(Elts);

  #######
  for n in [1..lnth+1] do
  boundaryList[n]:=[];
  for k in [1..Dimension(n-1)] do
  tmp:=data[n][k].BoundaryImage;
  BI:=tmp.ListIFace;
  SGN:=tmp.ListSign;
  LstEl:=StructuralCopy(tmp.ListElt);
  Append(Elts,Difference(LstEl,Elts));
  for s in [1..Length(BI)] do
  BI[s]:=[SGN[s]*BI[s],Position(Elts,LstEl[s])];
  od;
  Add(boundaryList[n],BI);
  od;
  od;
  ####

  G:=C!.group;

  ####################
  Boundary:=function(n,k);
  if k>0 then
  return boundaryList[n+1][k];
  else
  return NegateWord(boundaryList[n+1][-k]);
  fi;
  end;
  ####################

  ####################
  Stabilizer:=function(n,k);
  return StabilizerGroups[n+1][k];
  end;
  ####################


  ####################
  Action:=function(n,k,g)
  return 1;
  end;



  #############################
  return Objectify(HapNonFreeResolution,
            rec(
            stabilizer:=Stabilizer,
            elts:=Elts,
            group:=G,
            length:=lnth,
            boundary:=Boundary,
            homotopy:=fail,
            action:=Action,
            dimension:=Dimension,
            torsion:=p,
            groupname:=groupName,
            torsionCells:=torsionCells,
            torsionPosition:=torsionPosition,
            originalData:=celldata,
            celldata:= data,
            numberOfTorsionCells:= numberOfTorsionCells,
            stabilizerCardinalities:= stabilizerCardinalities,
            warned:= warned,
            properties:=
            [["length",Maximum(1000,lnth)],
            ["characteristic",0],
            ["type","resolution"]]  ));

end);
