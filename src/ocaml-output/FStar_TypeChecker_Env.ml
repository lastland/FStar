open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | DoNotUnfoldPureLets 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe 
  | NBE 
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____37 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____43 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____49 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____69 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____75 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____81 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____87 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____93 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____99 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____106 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____122 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____144 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____166 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____185 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____191 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____197 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____203 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____209 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____215 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____221 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____227 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____233 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____239 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____245 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____251 -> false 
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
      | (Weak ,Weak ) -> true
      | (HNF ,HNF ) -> true
      | (Primops ,Primops ) -> true
      | (Eager_unfolding ,Eager_unfolding ) -> true
      | (Inlining ,Inlining ) -> true
      | (DoNotUnfoldPureLets ,DoNotUnfoldPureLets ) -> true
      | (UnfoldTac ,UnfoldTac ) -> true
      | (PureSubtermsWithinComputations ,PureSubtermsWithinComputations ) ->
          true
      | (Simplify ,Simplify ) -> true
      | (EraseUniverses ,EraseUniverses ) -> true
      | (AllowUnboundUniverses ,AllowUnboundUniverses ) -> true
      | (Reify ,Reify ) -> true
      | (CompressUvars ,CompressUvars ) -> true
      | (NoFullNorm ,NoFullNorm ) -> true
      | (CheckNoUvars ,CheckNoUvars ) -> true
      | (Unmeta ,Unmeta ) -> true
      | (Unascribe ,Unascribe ) -> true
      | (NBE ,NBE ) -> true
      | (Exclude s11,Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11,UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1,UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1,UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr lids1,UnfoldAttr lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | uu____286 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____307 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____313 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____319 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____326 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
  
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
  
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
    }
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
  
type name_prefix = Prims.string Prims.list
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap ;
  is_pattern: Prims.bool ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  nosynth: Prims.bool ;
  uvar_subtyping: Prims.bool ;
  weaken_comp_tys: Prims.bool ;
  tc_term:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
    ;
  use_bv_sorts: Prims.bool ;
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Util.smap ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  dep_graph: FStar_Parser_Dep.deps ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    }
and solver_t =
  {
  init: env -> unit ;
  push: Prims.string -> unit ;
  pop: Prims.string -> unit ;
  snapshot:
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2
    ;
  rollback:
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit
    ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
    ;
  solve:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit
    ;
  finish: unit -> unit ;
  refresh: unit -> unit }
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
    ;
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range ;
  imp_meta:
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
    }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__attrtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__admit
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__lax
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__uvar_subtyping
  
let (__proj__Mkenv__item__weaken_comp_tys : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__weaken_comp_tys
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__normalized_eff_names
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__synth_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__splice
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dsenv
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dep_graph
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        weaken_comp_tys = __fname__weaken_comp_tys;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__nbe
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t ->
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__snapshot
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__rollback
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
  
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
  
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_range
  
let (__proj__Mkimplicit__item__imp_meta :
  implicit ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_meta
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type solver_depth_t =
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
type implicits = implicit Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___223_10073  ->
              match uu___223_10073 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____10076 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____10076  in
                  let uu____10077 =
                    let uu____10078 = FStar_Syntax_Subst.compress y  in
                    uu____10078.FStar_Syntax_Syntax.n  in
                  (match uu____10077 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____10082 =
                         let uu___237_10083 = y1  in
                         let uu____10084 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___237_10083.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___237_10083.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____10084
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____10082
                   | uu____10087 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___238_10099 = env  in
      let uu____10100 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___238_10099.solver);
        range = (uu___238_10099.range);
        curmodule = (uu___238_10099.curmodule);
        gamma = uu____10100;
        gamma_sig = (uu___238_10099.gamma_sig);
        gamma_cache = (uu___238_10099.gamma_cache);
        modules = (uu___238_10099.modules);
        expected_typ = (uu___238_10099.expected_typ);
        sigtab = (uu___238_10099.sigtab);
        attrtab = (uu___238_10099.attrtab);
        is_pattern = (uu___238_10099.is_pattern);
        instantiate_imp = (uu___238_10099.instantiate_imp);
        effects = (uu___238_10099.effects);
        generalize = (uu___238_10099.generalize);
        letrecs = (uu___238_10099.letrecs);
        top_level = (uu___238_10099.top_level);
        check_uvars = (uu___238_10099.check_uvars);
        use_eq = (uu___238_10099.use_eq);
        is_iface = (uu___238_10099.is_iface);
        admit = (uu___238_10099.admit);
        lax = (uu___238_10099.lax);
        lax_universes = (uu___238_10099.lax_universes);
        phase1 = (uu___238_10099.phase1);
        failhard = (uu___238_10099.failhard);
        nosynth = (uu___238_10099.nosynth);
        uvar_subtyping = (uu___238_10099.uvar_subtyping);
        weaken_comp_tys = (uu___238_10099.weaken_comp_tys);
        tc_term = (uu___238_10099.tc_term);
        type_of = (uu___238_10099.type_of);
        universe_of = (uu___238_10099.universe_of);
        check_type_of = (uu___238_10099.check_type_of);
        use_bv_sorts = (uu___238_10099.use_bv_sorts);
        qtbl_name_and_index = (uu___238_10099.qtbl_name_and_index);
        normalized_eff_names = (uu___238_10099.normalized_eff_names);
        proof_ns = (uu___238_10099.proof_ns);
        synth_hook = (uu___238_10099.synth_hook);
        splice = (uu___238_10099.splice);
        is_native_tactic = (uu___238_10099.is_native_tactic);
        identifier_info = (uu___238_10099.identifier_info);
        tc_hooks = (uu___238_10099.tc_hooks);
        dsenv = (uu___238_10099.dsenv);
        dep_graph = (uu___238_10099.dep_graph);
        nbe = (uu___238_10099.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____10107  -> fun uu____10108  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___239_10128 = env  in
      {
        solver = (uu___239_10128.solver);
        range = (uu___239_10128.range);
        curmodule = (uu___239_10128.curmodule);
        gamma = (uu___239_10128.gamma);
        gamma_sig = (uu___239_10128.gamma_sig);
        gamma_cache = (uu___239_10128.gamma_cache);
        modules = (uu___239_10128.modules);
        expected_typ = (uu___239_10128.expected_typ);
        sigtab = (uu___239_10128.sigtab);
        attrtab = (uu___239_10128.attrtab);
        is_pattern = (uu___239_10128.is_pattern);
        instantiate_imp = (uu___239_10128.instantiate_imp);
        effects = (uu___239_10128.effects);
        generalize = (uu___239_10128.generalize);
        letrecs = (uu___239_10128.letrecs);
        top_level = (uu___239_10128.top_level);
        check_uvars = (uu___239_10128.check_uvars);
        use_eq = (uu___239_10128.use_eq);
        is_iface = (uu___239_10128.is_iface);
        admit = (uu___239_10128.admit);
        lax = (uu___239_10128.lax);
        lax_universes = (uu___239_10128.lax_universes);
        phase1 = (uu___239_10128.phase1);
        failhard = (uu___239_10128.failhard);
        nosynth = (uu___239_10128.nosynth);
        uvar_subtyping = (uu___239_10128.uvar_subtyping);
        weaken_comp_tys = (uu___239_10128.weaken_comp_tys);
        tc_term = (uu___239_10128.tc_term);
        type_of = (uu___239_10128.type_of);
        universe_of = (uu___239_10128.universe_of);
        check_type_of = (uu___239_10128.check_type_of);
        use_bv_sorts = (uu___239_10128.use_bv_sorts);
        qtbl_name_and_index = (uu___239_10128.qtbl_name_and_index);
        normalized_eff_names = (uu___239_10128.normalized_eff_names);
        proof_ns = (uu___239_10128.proof_ns);
        synth_hook = (uu___239_10128.synth_hook);
        splice = (uu___239_10128.splice);
        is_native_tactic = (uu___239_10128.is_native_tactic);
        identifier_info = (uu___239_10128.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___239_10128.dsenv);
        dep_graph = (uu___239_10128.dep_graph);
        nbe = (uu___239_10128.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___240_10139 = e  in
      {
        solver = (uu___240_10139.solver);
        range = (uu___240_10139.range);
        curmodule = (uu___240_10139.curmodule);
        gamma = (uu___240_10139.gamma);
        gamma_sig = (uu___240_10139.gamma_sig);
        gamma_cache = (uu___240_10139.gamma_cache);
        modules = (uu___240_10139.modules);
        expected_typ = (uu___240_10139.expected_typ);
        sigtab = (uu___240_10139.sigtab);
        attrtab = (uu___240_10139.attrtab);
        is_pattern = (uu___240_10139.is_pattern);
        instantiate_imp = (uu___240_10139.instantiate_imp);
        effects = (uu___240_10139.effects);
        generalize = (uu___240_10139.generalize);
        letrecs = (uu___240_10139.letrecs);
        top_level = (uu___240_10139.top_level);
        check_uvars = (uu___240_10139.check_uvars);
        use_eq = (uu___240_10139.use_eq);
        is_iface = (uu___240_10139.is_iface);
        admit = (uu___240_10139.admit);
        lax = (uu___240_10139.lax);
        lax_universes = (uu___240_10139.lax_universes);
        phase1 = (uu___240_10139.phase1);
        failhard = (uu___240_10139.failhard);
        nosynth = (uu___240_10139.nosynth);
        uvar_subtyping = (uu___240_10139.uvar_subtyping);
        weaken_comp_tys = (uu___240_10139.weaken_comp_tys);
        tc_term = (uu___240_10139.tc_term);
        type_of = (uu___240_10139.type_of);
        universe_of = (uu___240_10139.universe_of);
        check_type_of = (uu___240_10139.check_type_of);
        use_bv_sorts = (uu___240_10139.use_bv_sorts);
        qtbl_name_and_index = (uu___240_10139.qtbl_name_and_index);
        normalized_eff_names = (uu___240_10139.normalized_eff_names);
        proof_ns = (uu___240_10139.proof_ns);
        synth_hook = (uu___240_10139.synth_hook);
        splice = (uu___240_10139.splice);
        is_native_tactic = (uu___240_10139.is_native_tactic);
        identifier_info = (uu___240_10139.identifier_info);
        tc_hooks = (uu___240_10139.tc_hooks);
        dsenv = (uu___240_10139.dsenv);
        dep_graph = g;
        nbe = (uu___240_10139.nbe)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun e  -> e.dep_graph 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____10162) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____10163,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____10164,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____10165 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____10174 . unit -> 'Auu____10174 FStar_Util.smap =
  fun uu____10181  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____10186 . unit -> 'Auu____10186 FStar_Util.smap =
  fun uu____10193  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
           FStar_Pervasives_Native.tuple3)
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
             FStar_Pervasives_Native.tuple3)
        ->
        (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
            ->
            solver_t ->
              FStar_Ident.lident ->
                (step Prims.list ->
                   env ->
                     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
                  -> env)
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun check_type_of  ->
            fun solver  ->
              fun module_lid  ->
                fun nbe1  ->
                  let uu____10327 = new_gamma_cache ()  in
                  let uu____10330 = new_sigtab ()  in
                  let uu____10333 = new_sigtab ()  in
                  let uu____10340 =
                    let uu____10353 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____10353, FStar_Pervasives_Native.None)  in
                  let uu____10368 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____10371 = FStar_Options.using_facts_from ()  in
                  let uu____10372 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____10375 = FStar_Syntax_DsEnv.empty_env ()  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10327;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10330;
                    attrtab = uu____10333;
                    is_pattern = false;
                    instantiate_imp = true;
                    effects = { decls = []; order = []; joins = [] };
                    generalize = true;
                    letrecs = [];
                    top_level = false;
                    check_uvars = false;
                    use_eq = false;
                    is_iface = false;
                    admit = false;
                    lax = false;
                    lax_universes = false;
                    phase1 = false;
                    failhard = false;
                    nosynth = false;
                    uvar_subtyping = true;
                    weaken_comp_tys = true;
                    tc_term;
                    type_of;
                    universe_of;
                    check_type_of;
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu____10340;
                    normalized_eff_names = uu____10368;
                    proof_ns = uu____10371;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10411  -> false);
                    identifier_info = uu____10372;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10375;
                    dep_graph = deps;
                    nbe = nbe1
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____10511  ->
    let uu____10512 = FStar_ST.op_Bang query_indices  in
    match uu____10512 with
    | [] -> failwith "Empty query indices!"
    | uu____10562 ->
        let uu____10571 =
          let uu____10580 =
            let uu____10587 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10587  in
          let uu____10637 = FStar_ST.op_Bang query_indices  in uu____10580 ::
            uu____10637
           in
        FStar_ST.op_Colon_Equals query_indices uu____10571
  
let (pop_query_indices : unit -> unit) =
  fun uu____10726  ->
    let uu____10727 = FStar_ST.op_Bang query_indices  in
    match uu____10727 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10842  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10872  ->
    match uu____10872 with
    | (l,n1) ->
        let uu____10879 = FStar_ST.op_Bang query_indices  in
        (match uu____10879 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10990 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____11009  ->
    let uu____11010 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____11010
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____11083 =
       let uu____11086 = FStar_ST.op_Bang stack  in env :: uu____11086  in
     FStar_ST.op_Colon_Equals stack uu____11083);
    (let uu___241_11135 = env  in
     let uu____11136 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____11139 = FStar_Util.smap_copy (sigtab env)  in
     let uu____11142 = FStar_Util.smap_copy (attrtab env)  in
     let uu____11149 =
       let uu____11162 =
         let uu____11165 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____11165  in
       let uu____11190 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____11162, uu____11190)  in
     let uu____11231 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____11234 =
       let uu____11237 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____11237  in
     {
       solver = (uu___241_11135.solver);
       range = (uu___241_11135.range);
       curmodule = (uu___241_11135.curmodule);
       gamma = (uu___241_11135.gamma);
       gamma_sig = (uu___241_11135.gamma_sig);
       gamma_cache = uu____11136;
       modules = (uu___241_11135.modules);
       expected_typ = (uu___241_11135.expected_typ);
       sigtab = uu____11139;
       attrtab = uu____11142;
       is_pattern = (uu___241_11135.is_pattern);
       instantiate_imp = (uu___241_11135.instantiate_imp);
       effects = (uu___241_11135.effects);
       generalize = (uu___241_11135.generalize);
       letrecs = (uu___241_11135.letrecs);
       top_level = (uu___241_11135.top_level);
       check_uvars = (uu___241_11135.check_uvars);
       use_eq = (uu___241_11135.use_eq);
       is_iface = (uu___241_11135.is_iface);
       admit = (uu___241_11135.admit);
       lax = (uu___241_11135.lax);
       lax_universes = (uu___241_11135.lax_universes);
       phase1 = (uu___241_11135.phase1);
       failhard = (uu___241_11135.failhard);
       nosynth = (uu___241_11135.nosynth);
       uvar_subtyping = (uu___241_11135.uvar_subtyping);
       weaken_comp_tys = (uu___241_11135.weaken_comp_tys);
       tc_term = (uu___241_11135.tc_term);
       type_of = (uu___241_11135.type_of);
       universe_of = (uu___241_11135.universe_of);
       check_type_of = (uu___241_11135.check_type_of);
       use_bv_sorts = (uu___241_11135.use_bv_sorts);
       qtbl_name_and_index = uu____11149;
       normalized_eff_names = uu____11231;
       proof_ns = (uu___241_11135.proof_ns);
       synth_hook = (uu___241_11135.synth_hook);
       splice = (uu___241_11135.splice);
       is_native_tactic = (uu___241_11135.is_native_tactic);
       identifier_info = uu____11234;
       tc_hooks = (uu___241_11135.tc_hooks);
       dsenv = (uu___241_11135.dsenv);
       dep_graph = (uu___241_11135.dep_graph);
       nbe = (uu___241_11135.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11283  ->
    let uu____11284 = FStar_ST.op_Bang stack  in
    match uu____11284 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11338 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2)
  = fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t =
  (Prims.int,Prims.int,solver_depth_t,Prims.int)
    FStar_Pervasives_Native.tuple4
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t,env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____11410  ->
           let uu____11411 = snapshot_stack env  in
           match uu____11411 with
           | (stack_depth,env1) ->
               let uu____11436 = snapshot_query_indices ()  in
               (match uu____11436 with
                | (query_indices_depth,()) ->
                    let uu____11460 = (env1.solver).snapshot msg  in
                    (match uu____11460 with
                     | (solver_depth,()) ->
                         let uu____11502 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11502 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___242_11548 = env1  in
                                 {
                                   solver = (uu___242_11548.solver);
                                   range = (uu___242_11548.range);
                                   curmodule = (uu___242_11548.curmodule);
                                   gamma = (uu___242_11548.gamma);
                                   gamma_sig = (uu___242_11548.gamma_sig);
                                   gamma_cache = (uu___242_11548.gamma_cache);
                                   modules = (uu___242_11548.modules);
                                   expected_typ =
                                     (uu___242_11548.expected_typ);
                                   sigtab = (uu___242_11548.sigtab);
                                   attrtab = (uu___242_11548.attrtab);
                                   is_pattern = (uu___242_11548.is_pattern);
                                   instantiate_imp =
                                     (uu___242_11548.instantiate_imp);
                                   effects = (uu___242_11548.effects);
                                   generalize = (uu___242_11548.generalize);
                                   letrecs = (uu___242_11548.letrecs);
                                   top_level = (uu___242_11548.top_level);
                                   check_uvars = (uu___242_11548.check_uvars);
                                   use_eq = (uu___242_11548.use_eq);
                                   is_iface = (uu___242_11548.is_iface);
                                   admit = (uu___242_11548.admit);
                                   lax = (uu___242_11548.lax);
                                   lax_universes =
                                     (uu___242_11548.lax_universes);
                                   phase1 = (uu___242_11548.phase1);
                                   failhard = (uu___242_11548.failhard);
                                   nosynth = (uu___242_11548.nosynth);
                                   uvar_subtyping =
                                     (uu___242_11548.uvar_subtyping);
                                   weaken_comp_tys =
                                     (uu___242_11548.weaken_comp_tys);
                                   tc_term = (uu___242_11548.tc_term);
                                   type_of = (uu___242_11548.type_of);
                                   universe_of = (uu___242_11548.universe_of);
                                   check_type_of =
                                     (uu___242_11548.check_type_of);
                                   use_bv_sorts =
                                     (uu___242_11548.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___242_11548.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___242_11548.normalized_eff_names);
                                   proof_ns = (uu___242_11548.proof_ns);
                                   synth_hook = (uu___242_11548.synth_hook);
                                   splice = (uu___242_11548.splice);
                                   is_native_tactic =
                                     (uu___242_11548.is_native_tactic);
                                   identifier_info =
                                     (uu___242_11548.identifier_info);
                                   tc_hooks = (uu___242_11548.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___242_11548.dep_graph);
                                   nbe = (uu___242_11548.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11579  ->
             let uu____11580 =
               match depth with
               | FStar_Pervasives_Native.Some (s1,s2,s3,s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None  ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None)
                in
             match uu____11580 with
             | (stack_depth,query_indices_depth,solver_depth,dsenv_depth) ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth  in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth  in
                             ((let uu____11706 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11706
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11717 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11717
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11744,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11776 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11802  ->
                  match uu____11802 with
                  | (m,uu____11808) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11776 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___243_11816 = env  in
               {
                 solver = (uu___243_11816.solver);
                 range = (uu___243_11816.range);
                 curmodule = (uu___243_11816.curmodule);
                 gamma = (uu___243_11816.gamma);
                 gamma_sig = (uu___243_11816.gamma_sig);
                 gamma_cache = (uu___243_11816.gamma_cache);
                 modules = (uu___243_11816.modules);
                 expected_typ = (uu___243_11816.expected_typ);
                 sigtab = (uu___243_11816.sigtab);
                 attrtab = (uu___243_11816.attrtab);
                 is_pattern = (uu___243_11816.is_pattern);
                 instantiate_imp = (uu___243_11816.instantiate_imp);
                 effects = (uu___243_11816.effects);
                 generalize = (uu___243_11816.generalize);
                 letrecs = (uu___243_11816.letrecs);
                 top_level = (uu___243_11816.top_level);
                 check_uvars = (uu___243_11816.check_uvars);
                 use_eq = (uu___243_11816.use_eq);
                 is_iface = (uu___243_11816.is_iface);
                 admit = (uu___243_11816.admit);
                 lax = (uu___243_11816.lax);
                 lax_universes = (uu___243_11816.lax_universes);
                 phase1 = (uu___243_11816.phase1);
                 failhard = (uu___243_11816.failhard);
                 nosynth = (uu___243_11816.nosynth);
                 uvar_subtyping = (uu___243_11816.uvar_subtyping);
                 weaken_comp_tys = (uu___243_11816.weaken_comp_tys);
                 tc_term = (uu___243_11816.tc_term);
                 type_of = (uu___243_11816.type_of);
                 universe_of = (uu___243_11816.universe_of);
                 check_type_of = (uu___243_11816.check_type_of);
                 use_bv_sorts = (uu___243_11816.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___243_11816.normalized_eff_names);
                 proof_ns = (uu___243_11816.proof_ns);
                 synth_hook = (uu___243_11816.synth_hook);
                 splice = (uu___243_11816.splice);
                 is_native_tactic = (uu___243_11816.is_native_tactic);
                 identifier_info = (uu___243_11816.identifier_info);
                 tc_hooks = (uu___243_11816.tc_hooks);
                 dsenv = (uu___243_11816.dsenv);
                 dep_graph = (uu___243_11816.dep_graph);
                 nbe = (uu___243_11816.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11829,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___244_11838 = env  in
               {
                 solver = (uu___244_11838.solver);
                 range = (uu___244_11838.range);
                 curmodule = (uu___244_11838.curmodule);
                 gamma = (uu___244_11838.gamma);
                 gamma_sig = (uu___244_11838.gamma_sig);
                 gamma_cache = (uu___244_11838.gamma_cache);
                 modules = (uu___244_11838.modules);
                 expected_typ = (uu___244_11838.expected_typ);
                 sigtab = (uu___244_11838.sigtab);
                 attrtab = (uu___244_11838.attrtab);
                 is_pattern = (uu___244_11838.is_pattern);
                 instantiate_imp = (uu___244_11838.instantiate_imp);
                 effects = (uu___244_11838.effects);
                 generalize = (uu___244_11838.generalize);
                 letrecs = (uu___244_11838.letrecs);
                 top_level = (uu___244_11838.top_level);
                 check_uvars = (uu___244_11838.check_uvars);
                 use_eq = (uu___244_11838.use_eq);
                 is_iface = (uu___244_11838.is_iface);
                 admit = (uu___244_11838.admit);
                 lax = (uu___244_11838.lax);
                 lax_universes = (uu___244_11838.lax_universes);
                 phase1 = (uu___244_11838.phase1);
                 failhard = (uu___244_11838.failhard);
                 nosynth = (uu___244_11838.nosynth);
                 uvar_subtyping = (uu___244_11838.uvar_subtyping);
                 weaken_comp_tys = (uu___244_11838.weaken_comp_tys);
                 tc_term = (uu___244_11838.tc_term);
                 type_of = (uu___244_11838.type_of);
                 universe_of = (uu___244_11838.universe_of);
                 check_type_of = (uu___244_11838.check_type_of);
                 use_bv_sorts = (uu___244_11838.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___244_11838.normalized_eff_names);
                 proof_ns = (uu___244_11838.proof_ns);
                 synth_hook = (uu___244_11838.synth_hook);
                 splice = (uu___244_11838.splice);
                 is_native_tactic = (uu___244_11838.is_native_tactic);
                 identifier_info = (uu___244_11838.identifier_info);
                 tc_hooks = (uu___244_11838.tc_hooks);
                 dsenv = (uu___244_11838.dsenv);
                 dep_graph = (uu___244_11838.dep_graph);
                 nbe = (uu___244_11838.nbe)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___245_11872 = e  in
         {
           solver = (uu___245_11872.solver);
           range = r;
           curmodule = (uu___245_11872.curmodule);
           gamma = (uu___245_11872.gamma);
           gamma_sig = (uu___245_11872.gamma_sig);
           gamma_cache = (uu___245_11872.gamma_cache);
           modules = (uu___245_11872.modules);
           expected_typ = (uu___245_11872.expected_typ);
           sigtab = (uu___245_11872.sigtab);
           attrtab = (uu___245_11872.attrtab);
           is_pattern = (uu___245_11872.is_pattern);
           instantiate_imp = (uu___245_11872.instantiate_imp);
           effects = (uu___245_11872.effects);
           generalize = (uu___245_11872.generalize);
           letrecs = (uu___245_11872.letrecs);
           top_level = (uu___245_11872.top_level);
           check_uvars = (uu___245_11872.check_uvars);
           use_eq = (uu___245_11872.use_eq);
           is_iface = (uu___245_11872.is_iface);
           admit = (uu___245_11872.admit);
           lax = (uu___245_11872.lax);
           lax_universes = (uu___245_11872.lax_universes);
           phase1 = (uu___245_11872.phase1);
           failhard = (uu___245_11872.failhard);
           nosynth = (uu___245_11872.nosynth);
           uvar_subtyping = (uu___245_11872.uvar_subtyping);
           weaken_comp_tys = (uu___245_11872.weaken_comp_tys);
           tc_term = (uu___245_11872.tc_term);
           type_of = (uu___245_11872.type_of);
           universe_of = (uu___245_11872.universe_of);
           check_type_of = (uu___245_11872.check_type_of);
           use_bv_sorts = (uu___245_11872.use_bv_sorts);
           qtbl_name_and_index = (uu___245_11872.qtbl_name_and_index);
           normalized_eff_names = (uu___245_11872.normalized_eff_names);
           proof_ns = (uu___245_11872.proof_ns);
           synth_hook = (uu___245_11872.synth_hook);
           splice = (uu___245_11872.splice);
           is_native_tactic = (uu___245_11872.is_native_tactic);
           identifier_info = (uu___245_11872.identifier_info);
           tc_hooks = (uu___245_11872.tc_hooks);
           dsenv = (uu___245_11872.dsenv);
           dep_graph = (uu___245_11872.dep_graph);
           nbe = (uu___245_11872.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11888 =
        let uu____11889 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11889 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11888
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11943 =
          let uu____11944 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11944 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11943
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11998 =
          let uu____11999 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11999 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11998
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____12053 =
        let uu____12054 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____12054 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____12053
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___246_12115 = env  in
      {
        solver = (uu___246_12115.solver);
        range = (uu___246_12115.range);
        curmodule = lid;
        gamma = (uu___246_12115.gamma);
        gamma_sig = (uu___246_12115.gamma_sig);
        gamma_cache = (uu___246_12115.gamma_cache);
        modules = (uu___246_12115.modules);
        expected_typ = (uu___246_12115.expected_typ);
        sigtab = (uu___246_12115.sigtab);
        attrtab = (uu___246_12115.attrtab);
        is_pattern = (uu___246_12115.is_pattern);
        instantiate_imp = (uu___246_12115.instantiate_imp);
        effects = (uu___246_12115.effects);
        generalize = (uu___246_12115.generalize);
        letrecs = (uu___246_12115.letrecs);
        top_level = (uu___246_12115.top_level);
        check_uvars = (uu___246_12115.check_uvars);
        use_eq = (uu___246_12115.use_eq);
        is_iface = (uu___246_12115.is_iface);
        admit = (uu___246_12115.admit);
        lax = (uu___246_12115.lax);
        lax_universes = (uu___246_12115.lax_universes);
        phase1 = (uu___246_12115.phase1);
        failhard = (uu___246_12115.failhard);
        nosynth = (uu___246_12115.nosynth);
        uvar_subtyping = (uu___246_12115.uvar_subtyping);
        weaken_comp_tys = (uu___246_12115.weaken_comp_tys);
        tc_term = (uu___246_12115.tc_term);
        type_of = (uu___246_12115.type_of);
        universe_of = (uu___246_12115.universe_of);
        check_type_of = (uu___246_12115.check_type_of);
        use_bv_sorts = (uu___246_12115.use_bv_sorts);
        qtbl_name_and_index = (uu___246_12115.qtbl_name_and_index);
        normalized_eff_names = (uu___246_12115.normalized_eff_names);
        proof_ns = (uu___246_12115.proof_ns);
        synth_hook = (uu___246_12115.synth_hook);
        splice = (uu___246_12115.splice);
        is_native_tactic = (uu___246_12115.is_native_tactic);
        identifier_info = (uu___246_12115.identifier_info);
        tc_hooks = (uu___246_12115.tc_hooks);
        dsenv = (uu___246_12115.dsenv);
        dep_graph = (uu___246_12115.dep_graph);
        nbe = (uu___246_12115.nbe)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12142 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____12142
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____12152 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____12152)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____12162 =
      let uu____12163 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____12163  in
    (FStar_Errors.Fatal_VariableNotFound, uu____12162)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____12168  ->
    let uu____12169 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____12169
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____12263) ->
          let vs = mk_univ_subst formals us  in
          let uu____12287 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12287)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___224_12303  ->
    match uu___224_12303 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12329  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun t  ->
      let uu____12348 = inst_tscheme t  in
      match uu____12348 with
      | (us,t1) ->
          let uu____12359 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12359)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12379  ->
          match uu____12379 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12400 =
                         let uu____12401 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12402 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12403 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12404 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12401 uu____12402 uu____12403 uu____12404
                          in
                       failwith uu____12400)
                    else ();
                    (let uu____12406 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12406))
               | uu____12415 ->
                   let uu____12416 =
                     let uu____12417 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12417
                      in
                   failwith uu____12416)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12423 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12429 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12435 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____12477) -> Maybe
             | (uu____12484,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12503 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____12594 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12594 with
          | FStar_Pervasives_Native.None  ->
              let uu____12617 =
                FStar_Util.find_map env.gamma
                  (fun uu___225_12661  ->
                     match uu___225_12661 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12700 = FStar_Ident.lid_equals lid l  in
                         if uu____12700
                         then
                           let uu____12721 =
                             let uu____12740 =
                               let uu____12755 = inst_tscheme t  in
                               FStar_Util.Inl uu____12755  in
                             let uu____12770 = FStar_Ident.range_of_lid l  in
                             (uu____12740, uu____12770)  in
                           FStar_Pervasives_Native.Some uu____12721
                         else FStar_Pervasives_Native.None
                     | uu____12822 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12617
                (fun uu____12860  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___226_12869  ->
                        match uu___226_12869 with
                        | (uu____12872,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12874);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12875;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12876;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12877;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12878;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12898 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12898
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids,s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____12946 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12953 -> cache t  in
                            let uu____12954 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12954 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12960 =
                                   let uu____12961 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12961)
                                    in
                                 maybe_cache uu____12960)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____13029 = find_in_sigtab env lid  in
         match uu____13029 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13109 = lookup_qname env lid  in
      match uu____13109 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____13130,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13241 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13241 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13283 =
          let uu____13286 = lookup_attr env1 attr  in se1 :: uu____13286  in
        FStar_Util.smap_add (attrtab env1) attr uu____13283  in
      FStar_List.iter
        (fun attr  ->
           let uu____13296 =
             let uu____13297 = FStar_Syntax_Subst.compress attr  in
             uu____13297.FStar_Syntax_Syntax.n  in
           match uu____13296 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13301 =
                 let uu____13302 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13302.FStar_Ident.str  in
               add_one1 env se uu____13301
           | uu____13303 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13325) ->
          add_sigelts env ses
      | uu____13334 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____13349 -> ()))

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___227_13380  ->
           match uu___227_13380 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13398 -> FStar_Pervasives_Native.None)
  
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____13459,lb::[]),uu____13461) ->
            let uu____13468 =
              let uu____13477 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13486 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13477, uu____13486)  in
            FStar_Pervasives_Native.Some uu____13468
        | FStar_Syntax_Syntax.Sig_let ((uu____13499,lbs),uu____13501) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13531 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13543 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13543
                     then
                       let uu____13554 =
                         let uu____13563 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13572 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13563, uu____13572)  in
                       FStar_Pervasives_Native.Some uu____13554
                     else FStar_Pervasives_Native.None)
        | uu____13594 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____13653 =
            let uu____13662 =
              let uu____13667 =
                let uu____13668 =
                  let uu____13671 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13671
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13668)  in
              inst_tscheme1 uu____13667  in
            (uu____13662, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13653
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13693,uu____13694) ->
          let uu____13699 =
            let uu____13708 =
              let uu____13713 =
                let uu____13714 =
                  let uu____13717 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13717  in
                (us, uu____13714)  in
              inst_tscheme1 uu____13713  in
            (uu____13708, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13699
      | uu____13736 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                          FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____13824 =
          match uu____13824 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13920,uvs,t,uu____13923,uu____13924,uu____13925);
                      FStar_Syntax_Syntax.sigrng = uu____13926;
                      FStar_Syntax_Syntax.sigquals = uu____13927;
                      FStar_Syntax_Syntax.sigmeta = uu____13928;
                      FStar_Syntax_Syntax.sigattrs = uu____13929;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13950 =
                     let uu____13959 = inst_tscheme1 (uvs, t)  in
                     (uu____13959, rng)  in
                   FStar_Pervasives_Native.Some uu____13950
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13983;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13985;
                      FStar_Syntax_Syntax.sigattrs = uu____13986;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____14003 =
                     let uu____14004 = in_cur_mod env l  in uu____14004 = Yes
                      in
                   if uu____14003
                   then
                     let uu____14015 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____14015
                      then
                        let uu____14028 =
                          let uu____14037 = inst_tscheme1 (uvs, t)  in
                          (uu____14037, rng)  in
                        FStar_Pervasives_Native.Some uu____14028
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____14068 =
                        let uu____14077 = inst_tscheme1 (uvs, t)  in
                        (uu____14077, rng)  in
                      FStar_Pervasives_Native.Some uu____14068)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14102,uu____14103);
                      FStar_Syntax_Syntax.sigrng = uu____14104;
                      FStar_Syntax_Syntax.sigquals = uu____14105;
                      FStar_Syntax_Syntax.sigmeta = uu____14106;
                      FStar_Syntax_Syntax.sigattrs = uu____14107;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____14148 =
                          let uu____14157 = inst_tscheme1 (uvs, k)  in
                          (uu____14157, rng)  in
                        FStar_Pervasives_Native.Some uu____14148
                    | uu____14178 ->
                        let uu____14179 =
                          let uu____14188 =
                            let uu____14193 =
                              let uu____14194 =
                                let uu____14197 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14197
                                 in
                              (uvs, uu____14194)  in
                            inst_tscheme1 uu____14193  in
                          (uu____14188, rng)  in
                        FStar_Pervasives_Native.Some uu____14179)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14220,uu____14221);
                      FStar_Syntax_Syntax.sigrng = uu____14222;
                      FStar_Syntax_Syntax.sigquals = uu____14223;
                      FStar_Syntax_Syntax.sigmeta = uu____14224;
                      FStar_Syntax_Syntax.sigattrs = uu____14225;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14267 =
                          let uu____14276 = inst_tscheme_with (uvs, k) us  in
                          (uu____14276, rng)  in
                        FStar_Pervasives_Native.Some uu____14267
                    | uu____14297 ->
                        let uu____14298 =
                          let uu____14307 =
                            let uu____14312 =
                              let uu____14313 =
                                let uu____14316 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14316
                                 in
                              (uvs, uu____14313)  in
                            inst_tscheme_with uu____14312 us  in
                          (uu____14307, rng)  in
                        FStar_Pervasives_Native.Some uu____14298)
               | FStar_Util.Inr se ->
                   let uu____14352 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14373;
                          FStar_Syntax_Syntax.sigrng = uu____14374;
                          FStar_Syntax_Syntax.sigquals = uu____14375;
                          FStar_Syntax_Syntax.sigmeta = uu____14376;
                          FStar_Syntax_Syntax.sigattrs = uu____14377;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14392 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14352
                     (FStar_Util.map_option
                        (fun uu____14440  ->
                           match uu____14440 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14471 =
          let uu____14482 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14482 mapper  in
        match uu____14471 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14556 =
              let uu____14567 =
                let uu____14574 =
                  let uu___247_14577 = t  in
                  let uu____14578 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___247_14577.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14578;
                    FStar_Syntax_Syntax.vars =
                      (uu___247_14577.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14574)  in
              (uu____14567, r)  in
            FStar_Pervasives_Native.Some uu____14556
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14625 = lookup_qname env l  in
      match uu____14625 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14644 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14696 = try_lookup_bv env bv  in
      match uu____14696 with
      | FStar_Pervasives_Native.None  ->
          let uu____14711 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14711 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14726 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14727 =
            let uu____14728 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14728  in
          (uu____14726, uu____14727)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14749 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14749 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14815 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14815  in
          let uu____14816 =
            let uu____14825 =
              let uu____14830 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14830)  in
            (uu____14825, r1)  in
          FStar_Pervasives_Native.Some uu____14816
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____14864 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14864 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14897,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14922 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14922  in
            let uu____14923 =
              let uu____14928 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14928, r1)  in
            FStar_Pervasives_Native.Some uu____14923
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14951 = try_lookup_lid env l  in
      match uu____14951 with
      | FStar_Pervasives_Native.None  ->
          let uu____14978 = name_not_found l  in
          let uu____14983 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14978 uu____14983
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___228_15023  ->
              match uu___228_15023 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____15025 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15044 = lookup_qname env lid  in
      match uu____15044 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15053,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15056;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15058;
              FStar_Syntax_Syntax.sigattrs = uu____15059;_},FStar_Pervasives_Native.None
            ),uu____15060)
          ->
          let uu____15109 =
            let uu____15116 =
              let uu____15117 =
                let uu____15120 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____15120 t  in
              (uvs, uu____15117)  in
            (uu____15116, q)  in
          FStar_Pervasives_Native.Some uu____15109
      | uu____15133 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15154 = lookup_qname env lid  in
      match uu____15154 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15159,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15162;
              FStar_Syntax_Syntax.sigquals = uu____15163;
              FStar_Syntax_Syntax.sigmeta = uu____15164;
              FStar_Syntax_Syntax.sigattrs = uu____15165;_},FStar_Pervasives_Native.None
            ),uu____15166)
          ->
          let uu____15215 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15215 (uvs, t)
      | uu____15220 ->
          let uu____15221 = name_not_found lid  in
          let uu____15226 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15221 uu____15226
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15245 = lookup_qname env lid  in
      match uu____15245 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15250,uvs,t,uu____15253,uu____15254,uu____15255);
              FStar_Syntax_Syntax.sigrng = uu____15256;
              FStar_Syntax_Syntax.sigquals = uu____15257;
              FStar_Syntax_Syntax.sigmeta = uu____15258;
              FStar_Syntax_Syntax.sigattrs = uu____15259;_},FStar_Pervasives_Native.None
            ),uu____15260)
          ->
          let uu____15313 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15313 (uvs, t)
      | uu____15318 ->
          let uu____15319 = name_not_found lid  in
          let uu____15324 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15319 uu____15324
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15345 = lookup_qname env lid  in
      match uu____15345 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15352,uu____15353,uu____15354,uu____15355,uu____15356,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15358;
              FStar_Syntax_Syntax.sigquals = uu____15359;
              FStar_Syntax_Syntax.sigmeta = uu____15360;
              FStar_Syntax_Syntax.sigattrs = uu____15361;_},uu____15362),uu____15363)
          -> (true, dcs)
      | uu____15424 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15437 = lookup_qname env lid  in
      match uu____15437 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15438,uu____15439,uu____15440,l,uu____15442,uu____15443);
              FStar_Syntax_Syntax.sigrng = uu____15444;
              FStar_Syntax_Syntax.sigquals = uu____15445;
              FStar_Syntax_Syntax.sigmeta = uu____15446;
              FStar_Syntax_Syntax.sigattrs = uu____15447;_},uu____15448),uu____15449)
          -> l
      | uu____15504 ->
          let uu____15505 =
            let uu____15506 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15506  in
          failwith uu____15505
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl))))
           in
        match qninfo with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15555)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15606,lbs),uu____15608)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15630 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15630
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15662 -> FStar_Pervasives_Native.None)
        | uu____15667 -> FStar_Pervasives_Native.None
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____15697 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15697
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15722),uu____15723) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15772 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15793),uu____15794) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15843 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15864 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15864
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15883 = lookup_qname env ftv  in
      match uu____15883 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15887) ->
          let uu____15932 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15932 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15953,t),r) ->
               let uu____15968 =
                 let uu____15969 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15969 t  in
               FStar_Pervasives_Native.Some uu____15968)
      | uu____15970 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15981 = try_lookup_effect_lid env ftv  in
      match uu____15981 with
      | FStar_Pervasives_Native.None  ->
          let uu____15984 = name_not_found ftv  in
          let uu____15989 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15984 uu____15989
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____16012 = lookup_qname env lid0  in
        match uu____16012 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____16023);
                FStar_Syntax_Syntax.sigrng = uu____16024;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____16026;
                FStar_Syntax_Syntax.sigattrs = uu____16027;_},FStar_Pervasives_Native.None
              ),uu____16028)
            ->
            let lid1 =
              let uu____16082 =
                let uu____16083 = FStar_Ident.range_of_lid lid  in
                let uu____16084 =
                  let uu____16085 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____16085  in
                FStar_Range.set_use_range uu____16083 uu____16084  in
              FStar_Ident.set_lid_range lid uu____16082  in
            let uu____16086 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___229_16090  ->
                      match uu___229_16090 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____16091 -> false))
               in
            if uu____16086
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____16105 =
                      let uu____16106 =
                        let uu____16107 = get_range env  in
                        FStar_Range.string_of_range uu____16107  in
                      let uu____16108 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____16109 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____16106 uu____16108 uu____16109
                       in
                    failwith uu____16105)
                  in
               match (binders, univs1) with
               | ([],uu____16126) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16151,uu____16152::uu____16153::uu____16154) ->
                   let uu____16175 =
                     let uu____16176 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____16177 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16176 uu____16177
                      in
                   failwith uu____16175
               | uu____16184 ->
                   let uu____16199 =
                     let uu____16204 =
                       let uu____16205 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____16205)  in
                     inst_tscheme_with uu____16204 insts  in
                   (match uu____16199 with
                    | (uu____16218,t) ->
                        let t1 =
                          let uu____16221 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16221 t  in
                        let uu____16222 =
                          let uu____16223 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16223.FStar_Syntax_Syntax.n  in
                        (match uu____16222 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16258 -> failwith "Impossible")))
        | uu____16265 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16288 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16288 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16301,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16308 = find1 l2  in
            (match uu____16308 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16315 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16315 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16319 = find1 l  in
            (match uu____16319 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16324 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16324
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16338 = lookup_qname env l1  in
      match uu____16338 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16341;
              FStar_Syntax_Syntax.sigrng = uu____16342;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16344;
              FStar_Syntax_Syntax.sigattrs = uu____16345;_},uu____16346),uu____16347)
          -> q
      | uu____16398 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16419 =
          let uu____16420 =
            let uu____16421 = FStar_Util.string_of_int i  in
            let uu____16422 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16421 uu____16422
             in
          failwith uu____16420  in
        let uu____16423 = lookup_datacon env lid  in
        match uu____16423 with
        | (uu____16428,t) ->
            let uu____16430 =
              let uu____16431 = FStar_Syntax_Subst.compress t  in
              uu____16431.FStar_Syntax_Syntax.n  in
            (match uu____16430 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16435) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16476 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16476
                      FStar_Pervasives_Native.fst)
             | uu____16487 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16498 = lookup_qname env l  in
      match uu____16498 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16499,uu____16500,uu____16501);
              FStar_Syntax_Syntax.sigrng = uu____16502;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16504;
              FStar_Syntax_Syntax.sigattrs = uu____16505;_},uu____16506),uu____16507)
          ->
          FStar_Util.for_some
            (fun uu___230_16560  ->
               match uu___230_16560 with
               | FStar_Syntax_Syntax.Projector uu____16561 -> true
               | uu____16566 -> false) quals
      | uu____16567 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16578 = lookup_qname env lid  in
      match uu____16578 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16579,uu____16580,uu____16581,uu____16582,uu____16583,uu____16584);
              FStar_Syntax_Syntax.sigrng = uu____16585;
              FStar_Syntax_Syntax.sigquals = uu____16586;
              FStar_Syntax_Syntax.sigmeta = uu____16587;
              FStar_Syntax_Syntax.sigattrs = uu____16588;_},uu____16589),uu____16590)
          -> true
      | uu____16645 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16656 = lookup_qname env lid  in
      match uu____16656 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16657,uu____16658,uu____16659,uu____16660,uu____16661,uu____16662);
              FStar_Syntax_Syntax.sigrng = uu____16663;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16665;
              FStar_Syntax_Syntax.sigattrs = uu____16666;_},uu____16667),uu____16668)
          ->
          FStar_Util.for_some
            (fun uu___231_16729  ->
               match uu___231_16729 with
               | FStar_Syntax_Syntax.RecordType uu____16730 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16739 -> true
               | uu____16748 -> false) quals
      | uu____16749 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16755,uu____16756);
            FStar_Syntax_Syntax.sigrng = uu____16757;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16759;
            FStar_Syntax_Syntax.sigattrs = uu____16760;_},uu____16761),uu____16762)
        ->
        FStar_Util.for_some
          (fun uu___232_16819  ->
             match uu___232_16819 with
             | FStar_Syntax_Syntax.Action uu____16820 -> true
             | uu____16821 -> false) quals
    | uu____16822 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16833 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16833
  
let (is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____16847 =
        let uu____16848 = FStar_Syntax_Util.un_uinst head1  in
        uu____16848.FStar_Syntax_Syntax.n  in
      match uu____16847 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16852 ->
               true
           | uu____16853 -> false)
      | uu____16854 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16865 = lookup_qname env l  in
      match uu____16865 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16867),uu____16868) ->
          FStar_Util.for_some
            (fun uu___233_16916  ->
               match uu___233_16916 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16917 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16918 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16989 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____17005) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____17022 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____17029 ->
                 FStar_Pervasives_Native.Some true
             | uu____17046 -> FStar_Pervasives_Native.Some false)
         in
      let uu____17047 =
        let uu____17050 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____17050 mapper  in
      match uu____17047 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____17102 = lookup_qname env lid  in
      match uu____17102 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17105,uu____17106,tps,uu____17108,uu____17109,uu____17110);
              FStar_Syntax_Syntax.sigrng = uu____17111;
              FStar_Syntax_Syntax.sigquals = uu____17112;
              FStar_Syntax_Syntax.sigmeta = uu____17113;
              FStar_Syntax_Syntax.sigattrs = uu____17114;_},uu____17115),uu____17116)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____17181 -> FStar_Pervasives_Native.None
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____17225  ->
              match uu____17225 with
              | (d,uu____17233) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17248 = effect_decl_opt env l  in
      match uu____17248 with
      | FStar_Pervasives_Native.None  ->
          let uu____17263 = name_not_found l  in
          let uu____17268 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17263 uu____17268
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17290  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17309  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17340 = FStar_Ident.lid_equals l1 l2  in
        if uu____17340
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17348 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17348
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17356 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17409  ->
                        match uu____17409 with
                        | (m1,m2,uu____17422,uu____17423,uu____17424) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17356 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17441 =
                    let uu____17446 =
                      let uu____17447 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17448 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17447
                        uu____17448
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17446)
                     in
                  FStar_Errors.raise_error uu____17441 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17455,uu____17456,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17489 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17489
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'Auu____17505 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17505)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17534 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17560  ->
                match uu____17560 with
                | (d,uu____17566) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17534 with
      | FStar_Pervasives_Native.None  ->
          let uu____17577 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17577
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17590 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17590 with
           | (uu____17605,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17623)::(wp,uu____17625)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17681 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          let uu____17736 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17736
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17738 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17738
             then
               FStar_Syntax_Syntax.mk_GTotal' res_t
                 (FStar_Pervasives_Native.Some res_u)
             else
               (let eff_name1 = norm_eff_name env eff_name  in
                let ed = get_effect_decl env eff_name1  in
                let null_wp =
                  inst_effect_fun_with [res_u] env ed
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let null_wp_res =
                  let uu____17746 = get_range env  in
                  let uu____17747 =
                    let uu____17754 =
                      let uu____17755 =
                        let uu____17772 =
                          let uu____17783 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17783]  in
                        (null_wp, uu____17772)  in
                      FStar_Syntax_Syntax.Tm_app uu____17755  in
                    FStar_Syntax_Syntax.mk uu____17754  in
                  uu____17747 FStar_Pervasives_Native.None uu____17746  in
                let uu____17823 =
                  let uu____17824 =
                    let uu____17835 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17835]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17824;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17823))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___248_17872 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___248_17872.order);
              joins = (uu___248_17872.joins)
            }  in
          let uu___249_17881 = env  in
          {
            solver = (uu___249_17881.solver);
            range = (uu___249_17881.range);
            curmodule = (uu___249_17881.curmodule);
            gamma = (uu___249_17881.gamma);
            gamma_sig = (uu___249_17881.gamma_sig);
            gamma_cache = (uu___249_17881.gamma_cache);
            modules = (uu___249_17881.modules);
            expected_typ = (uu___249_17881.expected_typ);
            sigtab = (uu___249_17881.sigtab);
            attrtab = (uu___249_17881.attrtab);
            is_pattern = (uu___249_17881.is_pattern);
            instantiate_imp = (uu___249_17881.instantiate_imp);
            effects;
            generalize = (uu___249_17881.generalize);
            letrecs = (uu___249_17881.letrecs);
            top_level = (uu___249_17881.top_level);
            check_uvars = (uu___249_17881.check_uvars);
            use_eq = (uu___249_17881.use_eq);
            is_iface = (uu___249_17881.is_iface);
            admit = (uu___249_17881.admit);
            lax = (uu___249_17881.lax);
            lax_universes = (uu___249_17881.lax_universes);
            phase1 = (uu___249_17881.phase1);
            failhard = (uu___249_17881.failhard);
            nosynth = (uu___249_17881.nosynth);
            uvar_subtyping = (uu___249_17881.uvar_subtyping);
            weaken_comp_tys = (uu___249_17881.weaken_comp_tys);
            tc_term = (uu___249_17881.tc_term);
            type_of = (uu___249_17881.type_of);
            universe_of = (uu___249_17881.universe_of);
            check_type_of = (uu___249_17881.check_type_of);
            use_bv_sorts = (uu___249_17881.use_bv_sorts);
            qtbl_name_and_index = (uu___249_17881.qtbl_name_and_index);
            normalized_eff_names = (uu___249_17881.normalized_eff_names);
            proof_ns = (uu___249_17881.proof_ns);
            synth_hook = (uu___249_17881.synth_hook);
            splice = (uu___249_17881.splice);
            is_native_tactic = (uu___249_17881.is_native_tactic);
            identifier_info = (uu___249_17881.identifier_info);
            tc_hooks = (uu___249_17881.tc_hooks);
            dsenv = (uu___249_17881.dsenv);
            dep_graph = (uu___249_17881.dep_graph);
            nbe = (uu___249_17881.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17911 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17911  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____18069 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____18070 = l1 u t wp e  in
                                l2 u t uu____18069 uu____18070))
                | uu____18071 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____18143 = inst_tscheme_with lift_t [u]  in
            match uu____18143 with
            | (uu____18150,lift_t1) ->
                let uu____18152 =
                  let uu____18159 =
                    let uu____18160 =
                      let uu____18177 =
                        let uu____18188 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18197 =
                          let uu____18208 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18208]  in
                        uu____18188 :: uu____18197  in
                      (lift_t1, uu____18177)  in
                    FStar_Syntax_Syntax.Tm_app uu____18160  in
                  FStar_Syntax_Syntax.mk uu____18159  in
                uu____18152 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____18320 = inst_tscheme_with lift_t [u]  in
            match uu____18320 with
            | (uu____18327,lift_t1) ->
                let uu____18329 =
                  let uu____18336 =
                    let uu____18337 =
                      let uu____18354 =
                        let uu____18365 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18374 =
                          let uu____18385 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18394 =
                            let uu____18405 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18405]  in
                          uu____18385 :: uu____18394  in
                        uu____18365 :: uu____18374  in
                      (lift_t1, uu____18354)  in
                    FStar_Syntax_Syntax.Tm_app uu____18337  in
                  FStar_Syntax_Syntax.mk uu____18336  in
                uu____18329 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____18507 =
                let uu____18508 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18508
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18507  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18512 =
              let uu____18513 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18513  in
            let uu____18514 =
              let uu____18515 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18541 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18541)
                 in
              FStar_Util.dflt "none" uu____18515  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18512
              uu____18514
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18567  ->
                    match uu____18567 with
                    | (e,uu____18575) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18598 =
            match uu____18598 with
            | (i,j) ->
                let uu____18609 = FStar_Ident.lid_equals i j  in
                if uu____18609
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____18641 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18651 = FStar_Ident.lid_equals i k  in
                        if uu____18651
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18662 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18662
                                  then []
                                  else
                                    (let uu____18666 =
                                       let uu____18675 =
                                         find_edge order1 (i, k)  in
                                       let uu____18678 =
                                         find_edge order1 (k, j)  in
                                       (uu____18675, uu____18678)  in
                                     match uu____18666 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18693 =
                                           compose_edges e1 e2  in
                                         [uu____18693]
                                     | uu____18694 -> [])))))
                 in
              FStar_List.append order1 uu____18641  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____18724 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18726 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18726
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18724
                   then
                     let uu____18731 =
                       let uu____18736 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18736)
                        in
                     let uu____18737 = get_range env  in
                     FStar_Errors.raise_error uu____18731 uu____18737
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18814 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18814
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18863 =
                                              let uu____18872 =
                                                find_edge order2 (i, k)  in
                                              let uu____18875 =
                                                find_edge order2 (j, k)  in
                                              (uu____18872, uu____18875)  in
                                            match uu____18863 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18917,uu____18918)
                                                     ->
                                                     let uu____18925 =
                                                       let uu____18930 =
                                                         let uu____18931 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18931
                                                          in
                                                       let uu____18934 =
                                                         let uu____18935 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18935
                                                          in
                                                       (uu____18930,
                                                         uu____18934)
                                                        in
                                                     (match uu____18925 with
                                                      | (true ,true ) ->
                                                          let uu____18946 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18946
                                                          then
                                                            (FStar_Errors.log_issue
                                                               FStar_Range.dummyRange
                                                               (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                 "Looking multiple times at the same upper bound candidate");
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____18971 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___250_19044 = env.effects  in
              { decls = (uu___250_19044.decls); order = order2; joins }  in
            let uu___251_19045 = env  in
            {
              solver = (uu___251_19045.solver);
              range = (uu___251_19045.range);
              curmodule = (uu___251_19045.curmodule);
              gamma = (uu___251_19045.gamma);
              gamma_sig = (uu___251_19045.gamma_sig);
              gamma_cache = (uu___251_19045.gamma_cache);
              modules = (uu___251_19045.modules);
              expected_typ = (uu___251_19045.expected_typ);
              sigtab = (uu___251_19045.sigtab);
              attrtab = (uu___251_19045.attrtab);
              is_pattern = (uu___251_19045.is_pattern);
              instantiate_imp = (uu___251_19045.instantiate_imp);
              effects;
              generalize = (uu___251_19045.generalize);
              letrecs = (uu___251_19045.letrecs);
              top_level = (uu___251_19045.top_level);
              check_uvars = (uu___251_19045.check_uvars);
              use_eq = (uu___251_19045.use_eq);
              is_iface = (uu___251_19045.is_iface);
              admit = (uu___251_19045.admit);
              lax = (uu___251_19045.lax);
              lax_universes = (uu___251_19045.lax_universes);
              phase1 = (uu___251_19045.phase1);
              failhard = (uu___251_19045.failhard);
              nosynth = (uu___251_19045.nosynth);
              uvar_subtyping = (uu___251_19045.uvar_subtyping);
              weaken_comp_tys = (uu___251_19045.weaken_comp_tys);
              tc_term = (uu___251_19045.tc_term);
              type_of = (uu___251_19045.type_of);
              universe_of = (uu___251_19045.universe_of);
              check_type_of = (uu___251_19045.check_type_of);
              use_bv_sorts = (uu___251_19045.use_bv_sorts);
              qtbl_name_and_index = (uu___251_19045.qtbl_name_and_index);
              normalized_eff_names = (uu___251_19045.normalized_eff_names);
              proof_ns = (uu___251_19045.proof_ns);
              synth_hook = (uu___251_19045.synth_hook);
              splice = (uu___251_19045.splice);
              is_native_tactic = (uu___251_19045.is_native_tactic);
              identifier_info = (uu___251_19045.identifier_info);
              tc_hooks = (uu___251_19045.tc_hooks);
              dsenv = (uu___251_19045.dsenv);
              dep_graph = (uu___251_19045.dep_graph);
              nbe = (uu___251_19045.nbe)
            }))
      | uu____19046 -> env
  
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____19074 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____19086 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____19086 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____19103 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____19103 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____19125 =
                     let uu____19130 =
                       let uu____19131 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____19138 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____19147 =
                         let uu____19148 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____19148  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____19131 uu____19138 uu____19147
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____19130)
                      in
                   FStar_Errors.raise_error uu____19125
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19153 =
                     let uu____19164 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____19164 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____19201  ->
                        fun uu____19202  ->
                          match (uu____19201, uu____19202) with
                          | ((x,uu____19232),(t,uu____19234)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19153
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19265 =
                     let uu___252_19266 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___252_19266.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___252_19266.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___252_19266.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___252_19266.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19265
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____19277 .
    'Auu____19277 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____19307 = effect_decl_opt env effect_name  in
          match uu____19307 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____19346 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19369 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____19406 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____19406
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____19407 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19407
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____19421 =
                     let uu____19424 = get_range env  in
                     let uu____19425 =
                       let uu____19432 =
                         let uu____19433 =
                           let uu____19450 =
                             let uu____19461 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____19461; wp]  in
                           (repr, uu____19450)  in
                         FStar_Syntax_Syntax.Tm_app uu____19433  in
                       FStar_Syntax_Syntax.mk uu____19432  in
                     uu____19425 FStar_Pervasives_Native.None uu____19424  in
                   FStar_Pervasives_Native.Some uu____19421)
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      (is_user_reifiable_effect env effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
  
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____19576 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19587 =
        let uu____19588 = FStar_Syntax_Subst.compress t  in
        uu____19588.FStar_Syntax_Syntax.n  in
      match uu____19587 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19591,c) ->
          is_reifiable_comp env c
      | uu____19613 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____19631 =
           let uu____19632 = is_reifiable_effect env l  in
           Prims.op_Negation uu____19632  in
         if uu____19631
         then
           let uu____19633 =
             let uu____19638 =
               let uu____19639 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19639
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19638)  in
           let uu____19640 = get_range env  in
           FStar_Errors.raise_error uu____19633 uu____19640
         else ());
        (let uu____19642 = effect_repr_aux true env c u_c  in
         match uu____19642 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___253_19674 = env  in
        {
          solver = (uu___253_19674.solver);
          range = (uu___253_19674.range);
          curmodule = (uu___253_19674.curmodule);
          gamma = (uu___253_19674.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___253_19674.gamma_cache);
          modules = (uu___253_19674.modules);
          expected_typ = (uu___253_19674.expected_typ);
          sigtab = (uu___253_19674.sigtab);
          attrtab = (uu___253_19674.attrtab);
          is_pattern = (uu___253_19674.is_pattern);
          instantiate_imp = (uu___253_19674.instantiate_imp);
          effects = (uu___253_19674.effects);
          generalize = (uu___253_19674.generalize);
          letrecs = (uu___253_19674.letrecs);
          top_level = (uu___253_19674.top_level);
          check_uvars = (uu___253_19674.check_uvars);
          use_eq = (uu___253_19674.use_eq);
          is_iface = (uu___253_19674.is_iface);
          admit = (uu___253_19674.admit);
          lax = (uu___253_19674.lax);
          lax_universes = (uu___253_19674.lax_universes);
          phase1 = (uu___253_19674.phase1);
          failhard = (uu___253_19674.failhard);
          nosynth = (uu___253_19674.nosynth);
          uvar_subtyping = (uu___253_19674.uvar_subtyping);
          weaken_comp_tys = (uu___253_19674.weaken_comp_tys);
          tc_term = (uu___253_19674.tc_term);
          type_of = (uu___253_19674.type_of);
          universe_of = (uu___253_19674.universe_of);
          check_type_of = (uu___253_19674.check_type_of);
          use_bv_sorts = (uu___253_19674.use_bv_sorts);
          qtbl_name_and_index = (uu___253_19674.qtbl_name_and_index);
          normalized_eff_names = (uu___253_19674.normalized_eff_names);
          proof_ns = (uu___253_19674.proof_ns);
          synth_hook = (uu___253_19674.synth_hook);
          splice = (uu___253_19674.splice);
          is_native_tactic = (uu___253_19674.is_native_tactic);
          identifier_info = (uu___253_19674.identifier_info);
          tc_hooks = (uu___253_19674.tc_hooks);
          dsenv = (uu___253_19674.dsenv);
          dep_graph = (uu___253_19674.dep_graph);
          nbe = (uu___253_19674.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___254_19687 = env  in
      {
        solver = (uu___254_19687.solver);
        range = (uu___254_19687.range);
        curmodule = (uu___254_19687.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___254_19687.gamma_sig);
        gamma_cache = (uu___254_19687.gamma_cache);
        modules = (uu___254_19687.modules);
        expected_typ = (uu___254_19687.expected_typ);
        sigtab = (uu___254_19687.sigtab);
        attrtab = (uu___254_19687.attrtab);
        is_pattern = (uu___254_19687.is_pattern);
        instantiate_imp = (uu___254_19687.instantiate_imp);
        effects = (uu___254_19687.effects);
        generalize = (uu___254_19687.generalize);
        letrecs = (uu___254_19687.letrecs);
        top_level = (uu___254_19687.top_level);
        check_uvars = (uu___254_19687.check_uvars);
        use_eq = (uu___254_19687.use_eq);
        is_iface = (uu___254_19687.is_iface);
        admit = (uu___254_19687.admit);
        lax = (uu___254_19687.lax);
        lax_universes = (uu___254_19687.lax_universes);
        phase1 = (uu___254_19687.phase1);
        failhard = (uu___254_19687.failhard);
        nosynth = (uu___254_19687.nosynth);
        uvar_subtyping = (uu___254_19687.uvar_subtyping);
        weaken_comp_tys = (uu___254_19687.weaken_comp_tys);
        tc_term = (uu___254_19687.tc_term);
        type_of = (uu___254_19687.type_of);
        universe_of = (uu___254_19687.universe_of);
        check_type_of = (uu___254_19687.check_type_of);
        use_bv_sorts = (uu___254_19687.use_bv_sorts);
        qtbl_name_and_index = (uu___254_19687.qtbl_name_and_index);
        normalized_eff_names = (uu___254_19687.normalized_eff_names);
        proof_ns = (uu___254_19687.proof_ns);
        synth_hook = (uu___254_19687.synth_hook);
        splice = (uu___254_19687.splice);
        is_native_tactic = (uu___254_19687.is_native_tactic);
        identifier_info = (uu___254_19687.identifier_info);
        tc_hooks = (uu___254_19687.tc_hooks);
        dsenv = (uu___254_19687.dsenv);
        dep_graph = (uu___254_19687.dep_graph);
        nbe = (uu___254_19687.nbe)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___255_19742 = env  in
             {
               solver = (uu___255_19742.solver);
               range = (uu___255_19742.range);
               curmodule = (uu___255_19742.curmodule);
               gamma = rest;
               gamma_sig = (uu___255_19742.gamma_sig);
               gamma_cache = (uu___255_19742.gamma_cache);
               modules = (uu___255_19742.modules);
               expected_typ = (uu___255_19742.expected_typ);
               sigtab = (uu___255_19742.sigtab);
               attrtab = (uu___255_19742.attrtab);
               is_pattern = (uu___255_19742.is_pattern);
               instantiate_imp = (uu___255_19742.instantiate_imp);
               effects = (uu___255_19742.effects);
               generalize = (uu___255_19742.generalize);
               letrecs = (uu___255_19742.letrecs);
               top_level = (uu___255_19742.top_level);
               check_uvars = (uu___255_19742.check_uvars);
               use_eq = (uu___255_19742.use_eq);
               is_iface = (uu___255_19742.is_iface);
               admit = (uu___255_19742.admit);
               lax = (uu___255_19742.lax);
               lax_universes = (uu___255_19742.lax_universes);
               phase1 = (uu___255_19742.phase1);
               failhard = (uu___255_19742.failhard);
               nosynth = (uu___255_19742.nosynth);
               uvar_subtyping = (uu___255_19742.uvar_subtyping);
               weaken_comp_tys = (uu___255_19742.weaken_comp_tys);
               tc_term = (uu___255_19742.tc_term);
               type_of = (uu___255_19742.type_of);
               universe_of = (uu___255_19742.universe_of);
               check_type_of = (uu___255_19742.check_type_of);
               use_bv_sorts = (uu___255_19742.use_bv_sorts);
               qtbl_name_and_index = (uu___255_19742.qtbl_name_and_index);
               normalized_eff_names = (uu___255_19742.normalized_eff_names);
               proof_ns = (uu___255_19742.proof_ns);
               synth_hook = (uu___255_19742.synth_hook);
               splice = (uu___255_19742.splice);
               is_native_tactic = (uu___255_19742.is_native_tactic);
               identifier_info = (uu___255_19742.identifier_info);
               tc_hooks = (uu___255_19742.tc_hooks);
               dsenv = (uu___255_19742.dsenv);
               dep_graph = (uu___255_19742.dep_graph);
               nbe = (uu___255_19742.nbe)
             }))
    | uu____19743 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19771  ->
             match uu____19771 with | (x,uu____19779) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___256_19813 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___256_19813.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___256_19813.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___257_19853 = env  in
       {
         solver = (uu___257_19853.solver);
         range = (uu___257_19853.range);
         curmodule = (uu___257_19853.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_19853.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___257_19853.sigtab);
         attrtab = (uu___257_19853.attrtab);
         is_pattern = (uu___257_19853.is_pattern);
         instantiate_imp = (uu___257_19853.instantiate_imp);
         effects = (uu___257_19853.effects);
         generalize = (uu___257_19853.generalize);
         letrecs = (uu___257_19853.letrecs);
         top_level = (uu___257_19853.top_level);
         check_uvars = (uu___257_19853.check_uvars);
         use_eq = (uu___257_19853.use_eq);
         is_iface = (uu___257_19853.is_iface);
         admit = (uu___257_19853.admit);
         lax = (uu___257_19853.lax);
         lax_universes = (uu___257_19853.lax_universes);
         phase1 = (uu___257_19853.phase1);
         failhard = (uu___257_19853.failhard);
         nosynth = (uu___257_19853.nosynth);
         uvar_subtyping = (uu___257_19853.uvar_subtyping);
         weaken_comp_tys = (uu___257_19853.weaken_comp_tys);
         tc_term = (uu___257_19853.tc_term);
         type_of = (uu___257_19853.type_of);
         universe_of = (uu___257_19853.universe_of);
         check_type_of = (uu___257_19853.check_type_of);
         use_bv_sorts = (uu___257_19853.use_bv_sorts);
         qtbl_name_and_index = (uu___257_19853.qtbl_name_and_index);
         normalized_eff_names = (uu___257_19853.normalized_eff_names);
         proof_ns = (uu___257_19853.proof_ns);
         synth_hook = (uu___257_19853.synth_hook);
         splice = (uu___257_19853.splice);
         is_native_tactic = (uu___257_19853.is_native_tactic);
         identifier_info = (uu___257_19853.identifier_info);
         tc_hooks = (uu___257_19853.tc_hooks);
         dsenv = (uu___257_19853.dsenv);
         dep_graph = (uu___257_19853.dep_graph);
         nbe = (uu___257_19853.nbe)
       })
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____19895 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19895 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19923 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19923)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___258_19938 = env  in
      {
        solver = (uu___258_19938.solver);
        range = (uu___258_19938.range);
        curmodule = (uu___258_19938.curmodule);
        gamma = (uu___258_19938.gamma);
        gamma_sig = (uu___258_19938.gamma_sig);
        gamma_cache = (uu___258_19938.gamma_cache);
        modules = (uu___258_19938.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___258_19938.sigtab);
        attrtab = (uu___258_19938.attrtab);
        is_pattern = (uu___258_19938.is_pattern);
        instantiate_imp = (uu___258_19938.instantiate_imp);
        effects = (uu___258_19938.effects);
        generalize = (uu___258_19938.generalize);
        letrecs = (uu___258_19938.letrecs);
        top_level = (uu___258_19938.top_level);
        check_uvars = (uu___258_19938.check_uvars);
        use_eq = false;
        is_iface = (uu___258_19938.is_iface);
        admit = (uu___258_19938.admit);
        lax = (uu___258_19938.lax);
        lax_universes = (uu___258_19938.lax_universes);
        phase1 = (uu___258_19938.phase1);
        failhard = (uu___258_19938.failhard);
        nosynth = (uu___258_19938.nosynth);
        uvar_subtyping = (uu___258_19938.uvar_subtyping);
        weaken_comp_tys = (uu___258_19938.weaken_comp_tys);
        tc_term = (uu___258_19938.tc_term);
        type_of = (uu___258_19938.type_of);
        universe_of = (uu___258_19938.universe_of);
        check_type_of = (uu___258_19938.check_type_of);
        use_bv_sorts = (uu___258_19938.use_bv_sorts);
        qtbl_name_and_index = (uu___258_19938.qtbl_name_and_index);
        normalized_eff_names = (uu___258_19938.normalized_eff_names);
        proof_ns = (uu___258_19938.proof_ns);
        synth_hook = (uu___258_19938.synth_hook);
        splice = (uu___258_19938.splice);
        is_native_tactic = (uu___258_19938.is_native_tactic);
        identifier_info = (uu___258_19938.identifier_info);
        tc_hooks = (uu___258_19938.tc_hooks);
        dsenv = (uu___258_19938.dsenv);
        dep_graph = (uu___258_19938.dep_graph);
        nbe = (uu___258_19938.nbe)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun env_  ->
    let uu____19966 = expected_typ env_  in
    ((let uu___259_19972 = env_  in
      {
        solver = (uu___259_19972.solver);
        range = (uu___259_19972.range);
        curmodule = (uu___259_19972.curmodule);
        gamma = (uu___259_19972.gamma);
        gamma_sig = (uu___259_19972.gamma_sig);
        gamma_cache = (uu___259_19972.gamma_cache);
        modules = (uu___259_19972.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___259_19972.sigtab);
        attrtab = (uu___259_19972.attrtab);
        is_pattern = (uu___259_19972.is_pattern);
        instantiate_imp = (uu___259_19972.instantiate_imp);
        effects = (uu___259_19972.effects);
        generalize = (uu___259_19972.generalize);
        letrecs = (uu___259_19972.letrecs);
        top_level = (uu___259_19972.top_level);
        check_uvars = (uu___259_19972.check_uvars);
        use_eq = false;
        is_iface = (uu___259_19972.is_iface);
        admit = (uu___259_19972.admit);
        lax = (uu___259_19972.lax);
        lax_universes = (uu___259_19972.lax_universes);
        phase1 = (uu___259_19972.phase1);
        failhard = (uu___259_19972.failhard);
        nosynth = (uu___259_19972.nosynth);
        uvar_subtyping = (uu___259_19972.uvar_subtyping);
        weaken_comp_tys = (uu___259_19972.weaken_comp_tys);
        tc_term = (uu___259_19972.tc_term);
        type_of = (uu___259_19972.type_of);
        universe_of = (uu___259_19972.universe_of);
        check_type_of = (uu___259_19972.check_type_of);
        use_bv_sorts = (uu___259_19972.use_bv_sorts);
        qtbl_name_and_index = (uu___259_19972.qtbl_name_and_index);
        normalized_eff_names = (uu___259_19972.normalized_eff_names);
        proof_ns = (uu___259_19972.proof_ns);
        synth_hook = (uu___259_19972.synth_hook);
        splice = (uu___259_19972.splice);
        is_native_tactic = (uu___259_19972.is_native_tactic);
        identifier_info = (uu___259_19972.identifier_info);
        tc_hooks = (uu___259_19972.tc_hooks);
        dsenv = (uu___259_19972.dsenv);
        dep_graph = (uu___259_19972.dep_graph);
        nbe = (uu___259_19972.nbe)
      }), uu____19966)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19982 =
      let uu____19985 = FStar_Ident.id_of_text ""  in [uu____19985]  in
    FStar_Ident.lid_of_ids uu____19982  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19991 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19991
        then
          let uu____19994 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19994 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___260_20021 = env  in
       {
         solver = (uu___260_20021.solver);
         range = (uu___260_20021.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___260_20021.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___260_20021.expected_typ);
         sigtab = (uu___260_20021.sigtab);
         attrtab = (uu___260_20021.attrtab);
         is_pattern = (uu___260_20021.is_pattern);
         instantiate_imp = (uu___260_20021.instantiate_imp);
         effects = (uu___260_20021.effects);
         generalize = (uu___260_20021.generalize);
         letrecs = (uu___260_20021.letrecs);
         top_level = (uu___260_20021.top_level);
         check_uvars = (uu___260_20021.check_uvars);
         use_eq = (uu___260_20021.use_eq);
         is_iface = (uu___260_20021.is_iface);
         admit = (uu___260_20021.admit);
         lax = (uu___260_20021.lax);
         lax_universes = (uu___260_20021.lax_universes);
         phase1 = (uu___260_20021.phase1);
         failhard = (uu___260_20021.failhard);
         nosynth = (uu___260_20021.nosynth);
         uvar_subtyping = (uu___260_20021.uvar_subtyping);
         weaken_comp_tys = (uu___260_20021.weaken_comp_tys);
         tc_term = (uu___260_20021.tc_term);
         type_of = (uu___260_20021.type_of);
         universe_of = (uu___260_20021.universe_of);
         check_type_of = (uu___260_20021.check_type_of);
         use_bv_sorts = (uu___260_20021.use_bv_sorts);
         qtbl_name_and_index = (uu___260_20021.qtbl_name_and_index);
         normalized_eff_names = (uu___260_20021.normalized_eff_names);
         proof_ns = (uu___260_20021.proof_ns);
         synth_hook = (uu___260_20021.synth_hook);
         splice = (uu___260_20021.splice);
         is_native_tactic = (uu___260_20021.is_native_tactic);
         identifier_info = (uu___260_20021.identifier_info);
         tc_hooks = (uu___260_20021.tc_hooks);
         dsenv = (uu___260_20021.dsenv);
         dep_graph = (uu___260_20021.dep_graph);
         nbe = (uu___260_20021.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20072)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20076,(uu____20077,t)))::tl1
          ->
          let uu____20098 =
            let uu____20101 = FStar_Syntax_Free.uvars t  in
            ext out uu____20101  in
          aux uu____20098 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20104;
            FStar_Syntax_Syntax.index = uu____20105;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20112 =
            let uu____20115 = FStar_Syntax_Free.uvars t  in
            ext out uu____20115  in
          aux uu____20112 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20172)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20176,(uu____20177,t)))::tl1
          ->
          let uu____20198 =
            let uu____20201 = FStar_Syntax_Free.univs t  in
            ext out uu____20201  in
          aux uu____20198 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20204;
            FStar_Syntax_Syntax.index = uu____20205;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20212 =
            let uu____20215 = FStar_Syntax_Free.univs t  in
            ext out uu____20215  in
          aux uu____20212 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____20276 = FStar_Util.set_add uname out  in
          aux uu____20276 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20279,(uu____20280,t)))::tl1
          ->
          let uu____20301 =
            let uu____20304 = FStar_Syntax_Free.univnames t  in
            ext out uu____20304  in
          aux uu____20301 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20307;
            FStar_Syntax_Syntax.index = uu____20308;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20315 =
            let uu____20318 = FStar_Syntax_Free.univnames t  in
            ext out uu____20318  in
          aux uu____20315 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___234_20338  ->
            match uu___234_20338 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20342 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20355 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20365 =
      let uu____20374 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20374
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20365 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20418 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___235_20428  ->
              match uu___235_20428 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20430 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20430
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20433) ->
                  let uu____20450 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20450))
       in
    FStar_All.pipe_right uu____20418 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___236_20457  ->
    match uu___236_20457 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20459 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20459
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20479  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20521) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20540,uu____20541) -> false  in
      let uu____20550 =
        FStar_List.tryFind
          (fun uu____20568  ->
             match uu____20568 with | (p,uu____20576) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20550 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20587,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20609 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20609
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___261_20627 = e  in
        {
          solver = (uu___261_20627.solver);
          range = (uu___261_20627.range);
          curmodule = (uu___261_20627.curmodule);
          gamma = (uu___261_20627.gamma);
          gamma_sig = (uu___261_20627.gamma_sig);
          gamma_cache = (uu___261_20627.gamma_cache);
          modules = (uu___261_20627.modules);
          expected_typ = (uu___261_20627.expected_typ);
          sigtab = (uu___261_20627.sigtab);
          attrtab = (uu___261_20627.attrtab);
          is_pattern = (uu___261_20627.is_pattern);
          instantiate_imp = (uu___261_20627.instantiate_imp);
          effects = (uu___261_20627.effects);
          generalize = (uu___261_20627.generalize);
          letrecs = (uu___261_20627.letrecs);
          top_level = (uu___261_20627.top_level);
          check_uvars = (uu___261_20627.check_uvars);
          use_eq = (uu___261_20627.use_eq);
          is_iface = (uu___261_20627.is_iface);
          admit = (uu___261_20627.admit);
          lax = (uu___261_20627.lax);
          lax_universes = (uu___261_20627.lax_universes);
          phase1 = (uu___261_20627.phase1);
          failhard = (uu___261_20627.failhard);
          nosynth = (uu___261_20627.nosynth);
          uvar_subtyping = (uu___261_20627.uvar_subtyping);
          weaken_comp_tys = (uu___261_20627.weaken_comp_tys);
          tc_term = (uu___261_20627.tc_term);
          type_of = (uu___261_20627.type_of);
          universe_of = (uu___261_20627.universe_of);
          check_type_of = (uu___261_20627.check_type_of);
          use_bv_sorts = (uu___261_20627.use_bv_sorts);
          qtbl_name_and_index = (uu___261_20627.qtbl_name_and_index);
          normalized_eff_names = (uu___261_20627.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___261_20627.synth_hook);
          splice = (uu___261_20627.splice);
          is_native_tactic = (uu___261_20627.is_native_tactic);
          identifier_info = (uu___261_20627.identifier_info);
          tc_hooks = (uu___261_20627.tc_hooks);
          dsenv = (uu___261_20627.dsenv);
          dep_graph = (uu___261_20627.dep_graph);
          nbe = (uu___261_20627.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___262_20667 = e  in
      {
        solver = (uu___262_20667.solver);
        range = (uu___262_20667.range);
        curmodule = (uu___262_20667.curmodule);
        gamma = (uu___262_20667.gamma);
        gamma_sig = (uu___262_20667.gamma_sig);
        gamma_cache = (uu___262_20667.gamma_cache);
        modules = (uu___262_20667.modules);
        expected_typ = (uu___262_20667.expected_typ);
        sigtab = (uu___262_20667.sigtab);
        attrtab = (uu___262_20667.attrtab);
        is_pattern = (uu___262_20667.is_pattern);
        instantiate_imp = (uu___262_20667.instantiate_imp);
        effects = (uu___262_20667.effects);
        generalize = (uu___262_20667.generalize);
        letrecs = (uu___262_20667.letrecs);
        top_level = (uu___262_20667.top_level);
        check_uvars = (uu___262_20667.check_uvars);
        use_eq = (uu___262_20667.use_eq);
        is_iface = (uu___262_20667.is_iface);
        admit = (uu___262_20667.admit);
        lax = (uu___262_20667.lax);
        lax_universes = (uu___262_20667.lax_universes);
        phase1 = (uu___262_20667.phase1);
        failhard = (uu___262_20667.failhard);
        nosynth = (uu___262_20667.nosynth);
        uvar_subtyping = (uu___262_20667.uvar_subtyping);
        weaken_comp_tys = (uu___262_20667.weaken_comp_tys);
        tc_term = (uu___262_20667.tc_term);
        type_of = (uu___262_20667.type_of);
        universe_of = (uu___262_20667.universe_of);
        check_type_of = (uu___262_20667.check_type_of);
        use_bv_sorts = (uu___262_20667.use_bv_sorts);
        qtbl_name_and_index = (uu___262_20667.qtbl_name_and_index);
        normalized_eff_names = (uu___262_20667.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___262_20667.synth_hook);
        splice = (uu___262_20667.splice);
        is_native_tactic = (uu___262_20667.is_native_tactic);
        identifier_info = (uu___262_20667.identifier_info);
        tc_hooks = (uu___262_20667.tc_hooks);
        dsenv = (uu___262_20667.dsenv);
        dep_graph = (uu___262_20667.dep_graph);
        nbe = (uu___262_20667.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20682 = FStar_Syntax_Free.names t  in
      let uu____20685 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20682 uu____20685
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20706 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20706
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20714 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20714
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20731 =
      match uu____20731 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20741 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20741)
       in
    let uu____20743 =
      let uu____20746 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20746 FStar_List.rev  in
    FStar_All.pipe_right uu____20743 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = [];
        univ_ineqs = ([],[]); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____20799 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20799 with
                   | FStar_Pervasives_Native.Some uu____20802 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20803 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20809;
        univ_ineqs = uu____20810; implicits = uu____20811;_} -> true
    | uu____20822 -> false
  
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___263_20849 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___263_20849.deferred);
            univ_ineqs = (uu___263_20849.univ_ineqs);
            implicits = (uu___263_20849.implicits)
          }
  
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____20884 = FStar_Options.defensive ()  in
          if uu____20884
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20888 =
              let uu____20889 =
                let uu____20890 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20890  in
              Prims.op_Negation uu____20889  in
            (if uu____20888
             then
               let uu____20895 =
                 let uu____20900 =
                   let uu____20901 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20902 =
                     let uu____20903 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20903
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20901 uu____20902
                    in
                 (FStar_Errors.Warning_Defensive, uu____20900)  in
               FStar_Errors.log_issue rng uu____20895
             else ())
          else ()
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____20934 =
            let uu____20935 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20935  in
          if uu____20934
          then ()
          else
            (let uu____20937 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20937 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20960 =
            let uu____20961 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20961  in
          if uu____20960
          then ()
          else
            (let uu____20963 = bound_vars e  in
             def_check_closed_in rng msg uu____20963 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___264_20998 = g  in
          let uu____20999 =
            let uu____21000 =
              let uu____21001 =
                let uu____21008 =
                  let uu____21009 =
                    let uu____21026 =
                      let uu____21037 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____21037]  in
                    (f, uu____21026)  in
                  FStar_Syntax_Syntax.Tm_app uu____21009  in
                FStar_Syntax_Syntax.mk uu____21008  in
              uu____21001 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____21000
             in
          {
            guard_f = uu____20999;
            deferred = (uu___264_20998.deferred);
            univ_ineqs = (uu___264_20998.univ_ineqs);
            implicits = (uu___264_20998.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___265_21093 = g  in
          let uu____21094 =
            let uu____21095 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____21095  in
          {
            guard_f = uu____21094;
            deferred = (uu___265_21093.deferred);
            univ_ineqs = (uu___265_21093.univ_ineqs);
            implicits = (uu___265_21093.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___266_21111 = g  in
          let uu____21112 =
            let uu____21113 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____21113  in
          {
            guard_f = uu____21112;
            deferred = (uu___266_21111.deferred);
            univ_ineqs = (uu___266_21111.univ_ineqs);
            implicits = (uu___266_21111.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___267_21115 = g  in
          let uu____21116 =
            let uu____21117 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____21117  in
          {
            guard_f = uu____21116;
            deferred = (uu___267_21115.deferred);
            univ_ineqs = (uu___267_21115.univ_ineqs);
            implicits = (uu___267_21115.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____21123 ->
        failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____21138 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____21138
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____21144 =
      let uu____21145 = FStar_Syntax_Util.unmeta t  in
      uu____21145.FStar_Syntax_Syntax.n  in
    match uu____21144 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21149 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____21190 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____21190;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____21271 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21271
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___268_21275 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___268_21275.deferred);
              univ_ineqs = (uu___268_21275.univ_ineqs);
              implicits = (uu___268_21275.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____21308 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21308
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___269_21331 = g  in
            let uu____21332 =
              let uu____21333 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21333  in
            {
              guard_f = uu____21332;
              deferred = (uu___269_21331.deferred);
              univ_ineqs = (uu___269_21331.univ_ineqs);
              implicits = (uu___269_21331.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,guard_t)
              FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            let uu____21371 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21371 with
            | FStar_Pervasives_Native.Some
                (uu____21396::(tm,uu____21398)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21462 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21480 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21480;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                   true gamma binders;
                 (let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_uvar
                         (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                      FStar_Pervasives_Native.None r
                     in
                  let imp =
                    {
                      imp_reason = reason;
                      imp_uvar = ctx_uvar;
                      imp_tm = t;
                      imp_range = r;
                      imp_meta = FStar_Pervasives_Native.None
                    }  in
                  let g =
                    let uu___270_21515 = trivial_guard  in
                    {
                      guard_f = (uu___270_21515.guard_f);
                      deferred = (uu___270_21515.deferred);
                      univ_ineqs = (uu___270_21515.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21532  -> ());
    push = (fun uu____21534  -> ());
    pop = (fun uu____21536  -> ());
    snapshot =
      (fun uu____21538  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21547  -> fun uu____21548  -> ());
    encode_modul = (fun uu____21559  -> fun uu____21560  -> ());
    encode_sig = (fun uu____21563  -> fun uu____21564  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21570 =
             let uu____21577 = FStar_Options.peek ()  in (e, g, uu____21577)
              in
           [uu____21570]);
    solve = (fun uu____21593  -> fun uu____21594  -> fun uu____21595  -> ());
    finish = (fun uu____21601  -> ());
    refresh = (fun uu____21603  -> ())
  } 