// line 27 requires downloading the appropriate cmf data

intrinsic X0DNdata(DBound::RngIntElt, NBound::RngIntElt : verbose:=true) -> Any
    {Outputs data table for the shimura curves X0(D;N), where D a quaternion discriminant and N coprime to D in the box D =< DBound and N <= NBound.}

    filename := Sprintf("./data/genera-tables/SignatureTableX0DN_%o_%o.txt", DBound, NBound);

    // Collect already-computed mu_labels (field 40) so we can resume without recomputing.
    done_keys := {};
    file_exists := false;
    try
        f := Open(filename, "r"); delete f;
        file_exists := true;
    catch e
        file_exists := false;
    end try;
    if file_exists then
        f := Open(filename, "r");
        line := Gets(f);
        while not IsEof(line) do
            parts := Split(line, "|");
            if #parts ge 40 and #parts[1] gt 0 and parts[1][1] ge "0" and parts[1][1] le "9" then
                Include(~done_keys, parts[40]);
            end if;
            line := Gets(f);
        end while;
        delete f;
    else
        f := Open(filename, "w"); delete f;
        fprintf filename, "label|Glabel|all_degree1_points_known|autmuO_norms|bad_primes|cm_discriminants|coarse_class|coarse_class_num|coarse_index|coarse_label|coarse_num|conductor|curve_label|deg_mu|dims|discB|discO|fine_label|fine_num|fuchsian_index|galEnd|generators|genus|genus_minus_rank|gerbiness|aut_gerbiness|has_obstruction|index|is_coarse|is_split|lattice_labels|lattice_x|level|level_is_squarefree|level_radical|level_is_prime|level_is_prime_power|log_conductor|models|mu_label|mults|name|newforms|nu2|nu3|nu4|nu6|num_bad_primes|num_known_degree1_noncm_points|num_known_degree1_points|obstructions|order_label|parents|parents_conj|pointless|power|psl2label|q_gonality|q_gonality_bounds|qbar_gonality|qbar_gonality_bounds|ram_data_elts|rank|reductions|scalar_label|simple|squarefree|torsion|trace_hash|traces\n";
        fprintf filename, "text|text|boolean|integer[]|integer[]|integer[]|text|integer|integer|text|integer|integer[]|text|integer|integer[]|integer|integer|text|integer|integer|text|integer[]|integer|integer|integer|integer|smallint|integer|boolean|boolean|text[]|integer[]|integer|boolean|integer|boolean|boolean|numeric|smallint|text|integer[]|text|text[]|integer|integer|integer|integer|integer|integer|integer|integer[]|text|text[]|integer[]|boolean|boolean|text|integer|integer[]|integer|integer[]|numeric[]|integer|text[]|text|boolean|boolean|integer[]|bigint|integer[]\n\n";
    end if;
    // Preload AutmuO sizes and mu from precomputed polarized data to avoid live recomputation.
    // Maximal orders (N=1): keyed by D (integer), from quaternion-maximal-orders-polarized.txt.
    // Eichler orders (N>1): keyed by order_label "D.DN" (string), from quaternion-Eichler-orders-polarized.txt.
    pol_autmuO_size  := AssociativeArray(Integers());
    pol_mu           := AssociativeArray(Integers());
    eich_autmuO_size := AssociativeArray();
    eich_mu          := AssociativeArray();

    pol_file := Open("./data/quaternion-orders/quaternion-maximal-orders-polarized.txt", "r");
    _ := Gets(pol_file); // header row
    _ := Gets(pol_file); // type row
    _ := Gets(pol_file); // blank line
    pol_line := Gets(pol_file);
    while not IsEof(pol_line) do
        if #pol_line gt 0 then
            fields := Split(pol_line, "|");
            if #fields ge 6 and StringToInteger(fields[4]) eq 1 and not ("." in fields[2]) then
                D_key := StringToInteger(fields[2]);
                pol_autmuO_size[D_key] := StringToInteger(fields[6]);
                pol_mu[D_key]          := fields[3];
            end if;
        end if;
        pol_line := Gets(pol_file);
    end while;
    delete pol_file;

    eich_file_exists := false;
    try
        f := Open("./data/quaternion-orders/quaternion-Eichler-orders-polarized.txt", "r"); delete f;
        eich_file_exists := true;
    catch e
        eich_file_exists := false;
    end try;
    if eich_file_exists then
        eich_file := Open("./data/quaternion-orders/quaternion-Eichler-orders-polarized.txt", "r");
        _ := Gets(eich_file); // header row
        _ := Gets(eich_file); // type row
        _ := Gets(eich_file); // blank line
        eich_line := Gets(eich_file);
        while not IsEof(eich_line) do
            if #eich_line gt 0 then
                fields := Split(eich_line, "|");
                if #fields ge 6 and StringToInteger(fields[4]) eq 1 then
                    eich_autmuO_size[fields[2]] := StringToInteger(fields[6]);
                    eich_mu[fields[2]]          := fields[3];
                end if;
            end if;
            eich_line := Gets(eich_file);
        end while;
        delete eich_file;
    end if;

    // Preload order basis data from quaternion-orders.txt (keyed by "D.DN") so that
    // Eichler orders are reconstructed from the stored basis rather than recomputed.
    ord_data := AssociativeArray();
    try
        f := Open("./data/quaternion-orders/quaternion-orders.txt", "r"); delete f;
        f := Open("./data/quaternion-orders/quaternion-orders.txt", "r");
        _ := Gets(f); _ := Gets(f); _ := Gets(f); // header, types, blank
        line := Gets(f);
        while not IsEof(line) do
            if #line gt 0 then
                fields := Split(line, "|");
                if #fields ge 7 and #fields[1] gt 0 and fields[1][1] ge "0" and fields[1][1] le "9" then
                    ord_data[fields[1]] := <fields[2], fields[3], fields[6], fields[7]>;
                end if;
            end if;
            line := Gets(f);
        end while;
        delete f;
    catch e
        ord_data := AssociativeArray();
    end try;

    // we only want D square-free, with an even number of prime factors.
    for D in [D : D in [6..DBound] | MoebiusMu(D) eq 1] do
        // we want N that are coprime to D and square-free.
        for N in [N : N in [1..NBound] | GCD(D,N) eq 1] do
            if (Gcd(D,N) gt 1) or (not IsSquarefree(N)) then continue; end if; // D and N are artificially coprime, local ideal theory is simpler when N is squarefree
            if (D*N gt 400) or (N eq 1) then continue; end if; // a bound that we artificially impose
            if verbose then printf "D = %o, N = %o\n", D, N; end if;
            mu_key := N eq 1 select Sprintf("%o.1", D) else Sprintf("%o.%o.1", D, N);
            if mu_key in done_keys then
                if verbose then printf "Skipping %o (already computed)\n", mu_key; end if;
                continue;
            end if;
            X := CMFLoad(D, N : cmfdatafile := "./code/jacobian_decomp/cmfdata.txt", levelbound:=D*N);
            ord_label := Sprintf("%o.%o", D, D*N);
            if N gt 1 and IsDefined(ord_data, ord_label) then
                dat := ord_data[ord_label];
                i_sq := StringToInteger(dat[1]);
                j_sq := StringToInteger(dat[2]);
                B := QuaternionAlgebra(Rationals(), i_sq, j_sq);
                O_max := MaximalOrder(B);
                nums   := eval ReplaceString(ReplaceString(dat[3], "{", "["), "}", "]");
                denoms := eval ReplaceString(ReplaceString(dat[4], "{", "["), "}", "]");
                bas := Basis(B);
                gens_rat := [&+[nums[k][c]*bas[c] : c in [1..4]] / denoms[k] : k in [1..4]];
                O := QuaternionOrder([g : g in gens_rat]);
                if verbose then printf "found basis of O\n"; end if;
            else
                O := QuaternionOrder(D, N);
            end if;
            Gamma := FuchsianGroup(O : VerifyEichler := false);
            // e := EllipticInvariants(Gamma);
            Glabel:="1.1";
            all_degree1_points_known:="\\N";
            autmuO_norms:="\\N";
            bad_primes := "{" cat Join([Sprintf("%o", p) : p in PrimeDivisors(D*N)], ",") cat "}";
            cm_discriminants:="\\N";
            coarse_class:="a";
            coarse_class_num:="1";
            eich_key := Sprintf("%o.%o", D, D*N);
            if N eq 1 and IsDefined(pol_autmuO_size, D) then
                size_AutmuO := pol_autmuO_size[D];
                printf "AutmuO size %o found for D=%o, N=%o\n", size_AutmuO, D, N;
            elif N gt 1 and IsDefined(eich_autmuO_size, eich_key) then
                size_AutmuO := eich_autmuO_size[eich_key];
                printf "AutmuO size %o found for D=%o, N=%o\n", size_AutmuO, D, N;
            else
                _, mu := HasPolarizedElementOfDegree(O,1);
                AutmuO:=Domain(Aut(O,mu));
                size_AutmuO := #AutmuO;
            end if;
            coarse_index:=size_AutmuO;
            genus:=Genus(Gamma);
            newforms, mults, dims, conductor, rank, simple := JLDecomposition(D, N, X : g := genus);
            squarefree := &and[m eq 1 : m in mults] select "T" else "F";
            newforms := #newforms eq 0 select "{}" else "{" cat Join(newforms, ",") cat "}";
            mults := #mults eq 0 select "{}" else "{" cat Join([Sprintf("%o", m) : m in mults], ",") cat "}";
            dims := #dims eq 0 select "{}" else "{" cat Join([Sprintf("%o", d) : d in dims], ",") cat "}";
            conductor := #conductor eq 0 select "{}" else "{" cat Join(["{" cat Sprintf("%o", fac[1]) cat "," cat Sprintf("%o", fac[2]) cat "}" : fac in conductor], ",") cat "}";
            coarse_label:=Sprintf("1.%o.%o.%o.1", size_AutmuO, genus, coarse_class);
            coarse_num:=1;
            curve_label:="\\N";
            deg_mu:=1;
            discB:=D;
            discO:=D*N;
            fine_label:=coarse_label;
            fine_num:="\\N";
            fuchsian_index:=size_AutmuO; // Double check that this is the correct index
            galEnd:="\\N";
            generators:="\\N";
            genus_minus_rank:=genus - rank;
            // gerbiness = aut_gerbiness = 1 because the map
            // f: Aut_{±mu}(O) --> N_{B^x}(O)/Q^x is injective for all N
            gerbiness := 1;
            aut_gerbiness := 1;
            has_obstruction:="\\N";
            index:=size_AutmuO;
            is_coarse:="F";
            is_split:="\\N";
            lattice_labels:="\\N";
            lattice_x:="\\N";
            level:=N;
            level_is_squarefree:=IsSquarefree(N) select "T" else "F";
            level_radical:=&*PrimeDivisors(N);
            level_is_prime := IsPrime(N) select "T" else "F";
            level_is_prime_power := (N gt 1 and IsPrimePower(N)) select "T" else "F";
            log_conductor:="\\N";
            models:="\\N";
            name:=N eq 1 select Sprintf("X(%o;1)",D) else "X(" cat Sprintf("%o,%o;1)", D,N);
            nu2:=0; nu3:=0; nu4:=0; nu6:=0;
            for pair in EllipticInvariants(Gamma) do
                if pair[1] eq 2 then nu2 := pair[2];
                elif pair[1] eq 3 then nu3 := pair[2];
                elif pair[1] eq 4 then nu4 := pair[2];
                elif pair[1] eq 6 then nu6 := pair[2];
                end if;
            end for;
            num_bad_primes:=#PrimeDivisors(D*N);
            num_known_degree1_noncm_points:="\\N";
            num_known_degree1_points:="\\N";
            obstructions:="\\N";
            if N eq 1 then
                order_label:=Sprintf("%o",D);
            else
                order_label:=Sprintf("%o.%o",D,D*N);
            end if;
            mu_label:=order_label cat ".1";
            label:=mu_label cat "." cat coarse_label;
            parents:="\\N";
            parents_conj:="\\N";
            pointless:="\\N";
            power:="\\N";
            psl2label:=label;
            gonality_temp:=GonalityBoundListX0DN(D,N);
            q_gonality:=gonality_temp[1];
            q_gonality_bounds:=Sprintf("{%o,%o}",gonality_temp[2][1],gonality_temp[2][2]);
            qbar_gonality:=gonality_temp[3];
            qbar_gonality_bounds:=Sprintf("{%o,%o}",gonality_temp[4][1],gonality_temp[4][2]);
            ram_data_elts:="\\N";
            reductions:="\\N";
            scalar_label:="\\N";
            torsion:="\\N";
            trace_hash:="\\N";
            traces:="\\N";
            fprintf filename, Sprintf("%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o|%o\n",label,Glabel,all_degree1_points_known,autmuO_norms,bad_primes,cm_discriminants,coarse_class,coarse_class_num,coarse_index,coarse_label,coarse_num,conductor,curve_label,deg_mu,dims,discB,discO,fine_label,fine_num,fuchsian_index,galEnd,generators,genus,genus_minus_rank,gerbiness,aut_gerbiness,has_obstruction,index,is_coarse,is_split,lattice_labels,lattice_x,level,level_is_squarefree,level_radical,level_is_prime,level_is_prime_power,log_conductor,models,mu_label,mults,name,newforms,nu2,nu3,nu4,nu6,num_bad_primes,num_known_degree1_noncm_points,num_known_degree1_points,obstructions,order_label,parents,parents_conj,pointless,power,psl2label,q_gonality,q_gonality_bounds,qbar_gonality,qbar_gonality_bounds,ram_data_elts,rank,reductions,scalar_label,simple,squarefree,torsion,trace_hash,traces);
        end for;
    end for;
    return Sprint("Table produced :)");
end intrinsic;