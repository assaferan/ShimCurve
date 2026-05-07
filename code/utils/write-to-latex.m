




MakeGeneraTableOfGenus:= function(D,del,N : genus:=0, IsSplit:=true, torsion:=[ ])
  filename:=Sprintf("genera-tables/genera-D%o-deg%o-N%o.m",D,del,N);
  r:=Open(filename,"r");
  if torsion eq [] then    
    possible_tors:=[  [2],[2,2],[3],[2,3],[4], [2,4], [2,2,2], [2,2,3],[3,4],[4,4], [2,2,4] ];
  else 
    possible_tors:=torsion;
  end if;
  tors_latex:=[ "(\\Z/4\\Z)", "(\\Z/2\\Z) \\times (\\Z/4\\Z)", "(\\Z/2\\Z)^3", "(\\Z/2\\Z)^2 \\times (\\Z/3\\Z)", "(\\Z/3\\Z) \\times (\\Z/4\\Z)", "(\\Z/4\\Z)^2", "(\\Z/2\\Z)^2 \\times (\\Z/4\\Z)"];
  possible_endogroup:=  [ " C2^2 ", " D2 ", " D3 ", " S3 ", " D4 ", " D6 "];
  endogroup_latex:=     [    "D_2",   "D_2", "D_3",  "D_3", "D_4", "D_6" ];

  lines:=[];
  count:=0;
  while true do
    count:=count+1;
    line :=Gets(r);
    if IsEof(line) then
      break;
    end if;
    
    if count ge 7 then 
      //split:=Split(line,"<");
      //if split[1] notin lines then 
        //split[1];
        Append(~lines,line);
      //end if;
    end if;
  end while;


  tors_list:= [ eval(Split(line,"?")[4]) : line in lines ];
  ParallelSort(~tors_list,~lines);

  data1:=[];
  for line in lines do
    split:=Split(line,"?");
    tors:=eval(split[4]);
    endogroup:=split[5];

    if tors in possible_tors and endogroup in possible_endogroup then
      ind:=Index(possible_endogroup,endogroup);
      latex_group:=endogroup_latex[ind];
      
      norms:=eval(split[6]);
      fuchsindex:=eval(split[2]);
      g:=Integers()!eval(split[1]);
      Hsplit:=eval(split[7]);

      item:=< g, tors, latex_group, norms, split[7], fuchsindex>;
      Append(~data1,item);
    end if;
  end for;

  data2:=[];
  for item in data1 do 
    similar_items:=[ meti : meti in data1 | Prune(meti) eq Prune(item) ];
    similar_fuchs:=[ a[6] : a in similar_items ];
    ParallelSort(~similar_fuchs,~similar_items);
    if similar_items[1] notin data2 then 
      Append(~data2,similar_items[1]);
    end if;
  end for;


  for elt in data2 do 
    g:=elt[1];
    Hsplit:=eval(split[7]);
    torstex:=tors_latex[Index(possible_tors,elt[2])];
    if g eq genus and Hsplit eq IsSplit then 
      printf "& & & $ %o $ & $%o$ & $%o$ & $ %o $ & $%o$ \\\\\n", elt[1], torstex, elt[3], elt[4], elt[6];  
        //line;
    end if;
  end for;
  return "";
end function;


MakeGeneraTable :=function(D,del,N : genus_range:=[0..200], torsion:=[])
  for g in genus_range do
    tab:=MakeGeneraTableOfGenus(D,del,N : genus:=g,IsSplit:=true, torsion:=torsion); 
    tab:=MakeGeneraTableOfGenus(D,del,N : genus:=g,IsSplit:=false, torsion:=torsion); 
  end for;
  return "";
end function;



D:=6;
del:=2;
N:=4;
MakeGeneraTable(D,del,N : torsion:=[[4]], genus_range:=[0..2]);

invariants:=[ [4], [2,4], [2,2,2], [2,2,3],[3,4],[4,4], [2,2,4] ];

for D in [6] do 
  for N in [4,6] do 
    for del in [1,2] do 
      "\\\\ \n";
      printf "\\cline{1-8}\n";
      printf "\\\\ \n"; 
      printf "$%o$ & $%o$ & $%o$ & & & & & \\\\",  D, N, del;
      "\\cline{1-3}\\\\";
      tab:=MakeGeneraTable(D,del,N : genus_range:=[0..50], torsion:=invariants);
    end for;
  end for;
end for;
