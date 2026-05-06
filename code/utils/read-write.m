
intrinsic Read(line::MonStgElt) -> Rec
  {turn the line of data into a record}

  split:=Split(line,"?");

  genus:=Integers()!eval(split[1]);
  fuchsindex:=eval(split[2]);
  torsioninvariants:=eval(split[4]);
  endogroup:=split[5];
  AutmuOnorms:=eval(split[6]);
  Hsplit:=eval(split[7]);
  generators:=split[8];
  ramification_data:=eval(split[9]);

  RF := recformat< n : Integers(),
  genus,
  fuchsindex,
  torsioninvariants,
  endogroup,
  AutmuOnorms,
  Hsplit,
  generators,
  ramification_data
  >;

  s := rec< RF | >;
  s`genus:=genus;
  s`fuchsindex:=fuchsindex;
  s`torsioninvariants:=torsioninvariants;
  s`endogroup:=endogroup;
  s`AutmuOnorms:=AutmuOnorms;
  s`Hsplit:=Hsplit;
  s`generators:=generators;
  s`ramification_data := ramification_data;
  
  return s;
end intrinsic;


intrinsic GeneraTableToRecords(D::RngIntElt,del::RngIntElt,N::RngIntElt : genus:=-1, fuchsindex:=-1, endogroup:="any", torsioninvariants:=[-1], AutmuOnorms:={0}, sort:=true) -> Any 
  {}
  filename:=Sprintf("data/genera-tables/genera-D%o-deg%o-N%o.m",D,del,N);
  r:=Open(filename,"r");

  records:=[];
  //i:=1;
  while true do
    line :=Gets(r);
    if IsEof(line) then
      break;
    end if;

    //if i eq 1 then 
     // ;
    //end if;

    if "<" in line and "QuaternionAlgebra" notin line then 
      s:=Read(line);
      if (s`genus eq genus or genus eq -1) 
        and (s`fuchsindex eq fuchsindex or fuchsindex eq -1)
         and (torsioninvariants eq [-1] or torsioninvariants eq s`torsioninvariants)  
          and (endogroup eq "any" or s`endogroup eq endogroup) 
            and (s`AutmuOnorms eq AutmuOnorms or AutmuOnorms eq {0}) 
             then   
        Append(~records,s);
      end if;
    end if;
    //i:=i+1;
  end while;
  
  if sort eq true then 
    //sort by fuchsianindex
    fuchsindicies:= [ s`fuchsindex : s in records ];
    ParallelSort(~fuchsindicies,~records);
  end if;
  return records;
end intrinsic;


intrinsic AbelianInvariantsToLatex(T::SeqEnum) -> MonStgElt 
 {}
  list:=[  [2],[2,2],[3],[2,3],[4], [2,4], [2,2,2], [3,3], [2,2,3],[3,4],[4,4], [2,2,4], [2,3,3] ];
  list_latex:=[  "(\\Z/2\\Z)", "(\\Z/2\\Z)^2", "(\\Z/3\\Z)", "(\\Z/2\\Z) \\times (\\Z/3\\Z)" ,  "(\\Z/4\\Z)", 
  	"(\\Z/2\\Z) \\times (\\Z/4\\Z)", "(\\Z/2\\Z)^3", "(\\Z/3\\Z)^2", "(\\Z/2\\Z)^2 \\times (\\Z/3\\Z)", 
  	"(\\Z/3\\Z) \\times (\\Z/4\\Z)", "(\\Z/4\\Z)^2", "(\\Z/2\\Z)^2 \\times (\\Z/4\\Z)", "(\\Z/2\\Z) \\times (\\Z/3\\Z)^2"];
  
  index:=Index(list,T);
  return list_latex[index];
 end intrinsic;


intrinsic GroupToLatex(G::MonStgElt) -> MonStgElt
  {}

  possible_endogroup:=  [ " C2 ", " C2^2 ", " D2 ", " D3 ", " S3 ", " D4 ", " D6 "];
  endogroup_latex:=     [  "C_2",  "D_2",   "D_2", "D_3",  "D_3", "D_4", "D_6" ];

  index:=Index(possible_endogroup,G);
  return endogroup_latex[index];
end intrinsic;



