open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____34 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____64 -> false
  
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__smt_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                    FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,
                  worklist) FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                let ctx_uvar =
                  let uu____355 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____355;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                  true gamma binders;
                (let t =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uvar
                        (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                     FStar_Pervasives_Native.None r
                    in
                 let imp =
                   {
                     FStar_TypeChecker_Env.imp_reason = reason;
                     FStar_TypeChecker_Env.imp_uvar = ctx_uvar;
                     FStar_TypeChecker_Env.imp_tm = t;
                     FStar_TypeChecker_Env.imp_range = r;
                     FStar_TypeChecker_Env.imp_meta =
                       FStar_Pervasives_Native.None
                   }  in
                 (ctx_uvar, t,
                   (let uu___345_390 = wl  in
                    {
                      attempting = (uu___345_390.attempting);
                      wl_deferred = (uu___345_390.wl_deferred);
                      ctr = (uu___345_390.ctr);
                      defer_ok = (uu___345_390.defer_ok);
                      smt_ok = (uu___345_390.smt_ok);
                      tcenv = (uu___345_390.tcenv);
                      wl_implicits = (imp :: (wl.wl_implicits))
                    })))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,worklist)
            FStar_Pervasives_Native.tuple3)
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___346_422 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___346_422.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___346_422.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___346_422.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___346_422.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___346_422.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___346_422.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___346_422.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___346_422.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___346_422.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___346_422.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___346_422.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___346_422.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___346_422.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___346_422.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___346_422.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___346_422.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___346_422.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___346_422.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___346_422.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___346_422.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___346_422.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___346_422.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___346_422.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___346_422.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___346_422.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___346_422.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___346_422.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___346_422.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___346_422.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___346_422.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___346_422.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___346_422.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___346_422.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___346_422.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___346_422.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___346_422.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___346_422.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___346_422.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___346_422.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___346_422.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___346_422.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____424 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____424 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____461 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____491 -> false
  
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____516 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____522 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____528 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___313_543  ->
    match uu___313_543 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____549 = FStar_Syntax_Util.head_and_args t  in
    match uu____549 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____610 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____611 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____623 =
                     let uu____624 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____624  in
                   FStar_Util.format1 "@<%s>" uu____623
                in
             let uu____627 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____610 uu____611 uu____627
         | uu____628 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___314_638  ->
      match uu___314_638 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____642 =
            let uu____645 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____646 =
              let uu____649 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____650 =
                let uu____653 =
                  let uu____656 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____656]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____653
                 in
              uu____649 :: uu____650  in
            uu____645 :: uu____646  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____642
      | FStar_TypeChecker_Common.CProb p ->
          let uu____660 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____661 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____662 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____660 uu____661
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____662
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___315_672  ->
      match uu___315_672 with
      | UNIV (u,t) ->
          let x =
            let uu____676 = FStar_Options.hide_uvar_nums ()  in
            if uu____676
            then "?"
            else
              (let uu____678 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____678 FStar_Util.string_of_int)
             in
          let uu____679 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____679
      | TERM (u,t) ->
          let x =
            let uu____683 = FStar_Options.hide_uvar_nums ()  in
            if uu____683
            then "?"
            else
              (let uu____685 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____685 FStar_Util.string_of_int)
             in
          let uu____686 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____686
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____701 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____701 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____715 =
      let uu____718 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____718
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____715 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____731 .
    (FStar_Syntax_Syntax.term,'Auu____731) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____749 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____767  ->
              match uu____767 with
              | (x,uu____773) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____749 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = true;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____803 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____803
         then
           let uu____804 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____804
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___316_810  ->
    match uu___316_810 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____815 .
    'Auu____815 FStar_TypeChecker_Common.problem ->
      'Auu____815 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___347_827 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___347_827.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___347_827.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___347_827.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___347_827.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___347_827.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___347_827.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___347_827.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____834 .
    'Auu____834 FStar_TypeChecker_Common.problem ->
      'Auu____834 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___317_851  ->
    match uu___317_851 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___318_866  ->
    match uu___318_866 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___348_872 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___348_872.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___348_872.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___348_872.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___348_872.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___348_872.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___348_872.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___348_872.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___348_872.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___348_872.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___349_880 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___349_880.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___349_880.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___349_880.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___349_880.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___349_880.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___349_880.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___349_880.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___349_880.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___349_880.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___319_892  ->
      match uu___319_892 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___320_897  ->
    match uu___320_897 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___321_908  ->
    match uu___321_908 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___322_921  ->
    match uu___322_921 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___323_934  ->
    match uu___323_934 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___324_947  ->
    match uu___324_947 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___325_960  ->
    match uu___325_960 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___326_971  ->
    match uu___326_971 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____986 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____986) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1014 =
          let uu____1015 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1015  in
        if uu____1014
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1049)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1095 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1119 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1119]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1095
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1147 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1171 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1171]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1147
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1214 =
          let uu____1215 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1215  in
        if uu____1214
        then ()
        else
          (let uu____1217 =
             let uu____1220 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1220
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1217 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1266 =
          let uu____1267 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1267  in
        if uu____1266
        then ()
        else
          (let uu____1269 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1269)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1286 =
        let uu____1287 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1287  in
      if uu____1286
      then ()
      else
        (let msgf m =
           let uu____1295 =
             let uu____1296 =
               let uu____1297 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1297 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1296  in
           Prims.strcat msg uu____1295  in
         (let uu____1299 = msgf "scope"  in
          let uu____1300 = p_scope prob  in
          def_scope_wf uu____1299 (p_loc prob) uu____1300);
         (let uu____1312 = msgf "guard"  in
          def_check_scoped uu____1312 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1317 = msgf "lhs"  in
                def_check_scoped uu____1317 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1318 = msgf "rhs"  in
                def_check_scoped uu____1318 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1323 = msgf "lhs"  in
                def_check_scoped_comp uu____1323 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1324 = msgf "rhs"  in
                def_check_scoped_comp uu____1324 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___350_1340 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___350_1340.wl_deferred);
          ctr = (uu___350_1340.ctr);
          defer_ok = (uu___350_1340.defer_ok);
          smt_ok;
          tcenv = (uu___350_1340.tcenv);
          wl_implicits = (uu___350_1340.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1347 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1347,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___351_1370 = empty_worklist env  in
      let uu____1371 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1371;
        wl_deferred = (uu___351_1370.wl_deferred);
        ctr = (uu___351_1370.ctr);
        defer_ok = (uu___351_1370.defer_ok);
        smt_ok = (uu___351_1370.smt_ok);
        tcenv = (uu___351_1370.tcenv);
        wl_implicits = (uu___351_1370.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___352_1391 = wl  in
        {
          attempting = (uu___352_1391.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___352_1391.ctr);
          defer_ok = (uu___352_1391.defer_ok);
          smt_ok = (uu___352_1391.smt_ok);
          tcenv = (uu___352_1391.tcenv);
          wl_implicits = (uu___352_1391.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___353_1413 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___353_1413.wl_deferred);
         ctr = (uu___353_1413.ctr);
         defer_ok = (uu___353_1413.defer_ok);
         smt_ok = (uu___353_1413.smt_ok);
         tcenv = (uu___353_1413.tcenv);
         wl_implicits = (uu___353_1413.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1424 .
    worklist ->
      'Auu____1424 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1453 = FStar_Syntax_Util.type_u ()  in
          match uu____1453 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1465 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1465 with
               | (uu____1476,tt,wl1) ->
                   let uu____1479 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1479, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___327_1484  ->
    match uu___327_1484 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1500 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1500 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1510  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1604 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1604 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1604 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1604 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____1689 =
                          let uu____1698 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1698]  in
                        FStar_List.append scope uu____1689
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____1741 =
                      let uu____1744 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____1744  in
                    FStar_List.append uu____1741
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____1763 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1763 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____1782 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1782;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____1850 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1850 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu____1933 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1933 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____1969 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1969 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1969 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____1969 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2035 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2035]  in
                        let uu____2054 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2054
                     in
                  let uu____2057 =
                    let uu____2064 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___354_2074 = wl  in
                       {
                         attempting = (uu___354_2074.attempting);
                         wl_deferred = (uu___354_2074.wl_deferred);
                         ctr = (uu___354_2074.ctr);
                         defer_ok = (uu___354_2074.defer_ok);
                         smt_ok = (uu___354_2074.smt_ok);
                         tcenv = env;
                         wl_implicits = (uu___354_2074.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2064
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2057 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2086 =
                              let uu____2091 =
                                let uu____2092 =
                                  let uu____2101 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2101
                                   in
                                [uu____2092]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2091  in
                            uu____2086 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2131 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2131;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____2173 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2173;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'Auu____2185 .
    worklist ->
      'Auu____2185 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____2218 =
                let uu____2221 =
                  let uu____2222 =
                    let uu____2229 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2229)  in
                  FStar_Syntax_Syntax.NT uu____2222  in
                [uu____2221]  in
              FStar_Syntax_Subst.subst uu____2218 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2249 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2249
        then
          let uu____2250 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2251 = prob_to_string env d  in
          let uu____2252 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2250 uu____2251 uu____2252 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2258 -> failwith "impossible"  in
           let uu____2259 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2271 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2272 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2271, uu____2272)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2276 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2277 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2276, uu____2277)
              in
           match uu____2259 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___328_2295  ->
            match uu___328_2295 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2307 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2311 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2311 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___329_2340  ->
           match uu___329_2340 with
           | UNIV uu____2343 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2350 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2350
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___330_2374  ->
           match uu___330_2374 with
           | UNIV (u',t) ->
               let uu____2379 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2379
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2383 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2394 =
        let uu____2395 =
          let uu____2396 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2396
           in
        FStar_Syntax_Subst.compress uu____2395  in
      FStar_All.pipe_right uu____2394 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2407 =
        let uu____2408 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t
           in
        FStar_Syntax_Subst.compress uu____2408  in
      FStar_All.pipe_right uu____2407 FStar_Syntax_Util.unlazy_emb
  
let norm_arg :
  'Auu____2415 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2415) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2415)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2438 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2438, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____2489  ->
              match uu____2489 with
              | (x,imp) ->
                  let uu____2508 =
                    let uu___355_2509 = x  in
                    let uu____2510 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___355_2509.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___355_2509.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2510
                    }  in
                  (uu____2508, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2533 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2533
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2537 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2537
        | uu____2540 -> u2  in
      let uu____2541 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2541
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                    FStar_Pervasives_Native.tuple2
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF]  in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2653 = norm_refinement env t12  in
                 match uu____2653 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2668;
                     FStar_Syntax_Syntax.vars = uu____2669;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2693 =
                       let uu____2694 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2695 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2694 uu____2695
                        in
                     failwith uu____2693)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2709 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2709
          | FStar_Syntax_Syntax.Tm_uinst uu____2710 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2745 =
                   let uu____2746 = FStar_Syntax_Subst.compress t1'  in
                   uu____2746.FStar_Syntax_Syntax.n  in
                 match uu____2745 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2761 -> aux true t1'
                 | uu____2768 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2783 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2812 =
                   let uu____2813 = FStar_Syntax_Subst.compress t1'  in
                   uu____2813.FStar_Syntax_Syntax.n  in
                 match uu____2812 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2828 -> aux true t1'
                 | uu____2835 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2850 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2895 =
                   let uu____2896 = FStar_Syntax_Subst.compress t1'  in
                   uu____2896.FStar_Syntax_Syntax.n  in
                 match uu____2895 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2911 -> aux true t1'
                 | uu____2918 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2933 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2948 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2963 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2978 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2993 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3022 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3055 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3076 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3103 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3130 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3167 ->
              let uu____3174 =
                let uu____3175 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3176 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3175 uu____3176
                 in
              failwith uu____3174
          | FStar_Syntax_Syntax.Tm_ascribed uu____3189 ->
              let uu____3216 =
                let uu____3217 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3218 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3217 uu____3218
                 in
              failwith uu____3216
          | FStar_Syntax_Syntax.Tm_delayed uu____3231 ->
              let uu____3254 =
                let uu____3255 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3256 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3255 uu____3256
                 in
              failwith uu____3254
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3269 =
                let uu____3270 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3271 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3270 uu____3271
                 in
              failwith uu____3269
           in
        let uu____3284 = whnf env t1  in aux false uu____3284
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____3340 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3340 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3380 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3380, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____3404 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3404 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                          FStar_Syntax_Syntax.term)
                                                          FStar_Pervasives_Native.tuple2
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun uu____3463  ->
    match uu____3463 with
    | (t_base,refopt) ->
        let uu____3494 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3494 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3532 =
      let uu____3535 =
        let uu____3538 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3561  ->
                  match uu____3561 with | (uu____3568,uu____3569,x) -> x))
           in
        FStar_List.append wl.attempting uu____3538  in
      FStar_List.map (wl_prob_to_string wl) uu____3535  in
    FStar_All.pipe_right uu____3532 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3583 .
    ('Auu____3583,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3594  ->
    match uu____3594 with
    | (uu____3601,c,args) ->
        let uu____3604 = print_ctx_uvar c  in
        let uu____3605 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3604 uu____3605
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3611 = FStar_Syntax_Util.head_and_args t  in
    match uu____3611 with
    | (head1,_args) ->
        let uu____3654 =
          let uu____3655 = FStar_Syntax_Subst.compress head1  in
          uu____3655.FStar_Syntax_Syntax.n  in
        (match uu____3654 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3658 -> true
         | uu____3671 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3677 = FStar_Syntax_Util.head_and_args t  in
    match uu____3677 with
    | (head1,_args) ->
        let uu____3720 =
          let uu____3721 = FStar_Syntax_Subst.compress head1  in
          uu____3721.FStar_Syntax_Syntax.n  in
        (match uu____3720 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3725) -> u
         | uu____3742 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3765 = FStar_Syntax_Util.head_and_args t  in
      match uu____3765 with
      | (head1,args) ->
          let uu____3812 =
            let uu____3813 = FStar_Syntax_Subst.compress head1  in
            uu____3813.FStar_Syntax_Syntax.n  in
          (match uu____3812 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3821)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3854 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___331_3879  ->
                         match uu___331_3879 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3883 =
                               let uu____3884 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3884.FStar_Syntax_Syntax.n  in
                             (match uu____3883 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3888 -> false)
                         | uu____3889 -> true))
                  in
               (match uu____3854 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____3913 =
                        FStar_List.collect
                          (fun uu___332_3925  ->
                             match uu___332_3925 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____3929 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____3929]
                             | uu____3930 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____3913 FStar_List.rev  in
                    let uu____3953 =
                      let uu____3960 =
                        let uu____3969 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___333_3991  ->
                                  match uu___333_3991 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____3995 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____3995]
                                  | uu____3996 -> []))
                           in
                        FStar_All.pipe_right uu____3969 FStar_List.rev  in
                      let uu____4019 =
                        let uu____4022 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4022  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____3960 uu____4019
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____3953 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4057  ->
                                match uu____4057 with
                                | (x,i) ->
                                    let uu____4076 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4076, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4107  ->
                                match uu____4107 with
                                | (a,i) ->
                                    let uu____4126 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4126, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____4148 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4168 =
          let uu____4191 =
            let uu____4192 = FStar_Syntax_Subst.compress k  in
            uu____4192.FStar_Syntax_Syntax.n  in
          match uu____4191 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4273 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4273)
              else
                (let uu____4307 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4307 with
                 | (ys',t1,uu____4340) ->
                     let uu____4345 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4345))
          | uu____4384 ->
              let uu____4385 =
                let uu____4390 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4390)  in
              ((ys, t), uu____4385)
           in
        match uu____4168 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____4483 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4483 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____4557 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4557
                then
                  let uu____4558 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4559 = print_ctx_uvar uv  in
                  let uu____4560 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4558 uu____4559 uu____4560
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4566 =
                   let uu____4567 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4567  in
                 let uu____4568 =
                   let uu____4571 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4571
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4566 uu____4568 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4604 =
               let uu____4605 =
                 let uu____4606 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4607 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4606 uu____4607
                  in
               failwith uu____4605  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4671  ->
                       match uu____4671 with
                       | (a,i) ->
                           let uu____4692 =
                             let uu____4693 = FStar_Syntax_Subst.compress a
                                in
                             uu____4693.FStar_Syntax_Syntax.n  in
                           (match uu____4692 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4719 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4729 =
                 let uu____4730 = is_flex g  in Prims.op_Negation uu____4730
                  in
               if uu____4729
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4734 = destruct_flex_t g wl  in
                  match uu____4734 with
                  | ((uu____4739,uv1,args),wl1) ->
                      ((let uu____4744 = args_as_binders args  in
                        assign_solution uu____4744 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___356_4746 = wl1  in
              {
                attempting = (uu___356_4746.attempting);
                wl_deferred = (uu___356_4746.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___356_4746.defer_ok);
                smt_ok = (uu___356_4746.smt_ok);
                tcenv = (uu___356_4746.tcenv);
                wl_implicits = (uu___356_4746.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4767 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4767
         then
           let uu____4768 = FStar_Util.string_of_int pid  in
           let uu____4769 =
             let uu____4770 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4770 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4768 uu____4769
         else ());
        commit sol;
        (let uu___357_4777 = wl  in
         {
           attempting = (uu___357_4777.attempting);
           wl_deferred = (uu___357_4777.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___357_4777.defer_ok);
           smt_ok = (uu___357_4777.smt_ok);
           tcenv = (uu___357_4777.tcenv);
           wl_implicits = (uu___357_4777.wl_implicits)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____4839,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4867 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4867
              in
           (let uu____4873 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4873
            then
              let uu____4874 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4875 =
                let uu____4876 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4876 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4874 uu____4875
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____4901 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4901 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool,Prims.string
                                                            FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun uk  ->
    fun t  ->
      let uu____4935 = occurs uk t  in
      match uu____4935 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4964 =
                 let uu____4965 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4966 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4965 uu____4966
                  in
               FStar_Pervasives_Native.Some uu____4964)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,(FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.binders)
                                     FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5079 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5079 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5129 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5185  ->
             match uu____5185 with
             | (x,uu____5197) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5214 = FStar_List.last bs  in
      match uu____5214 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5238) ->
          let uu____5249 =
            FStar_Util.prefix_until
              (fun uu___334_5264  ->
                 match uu___334_5264 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5266 -> false) g
             in
          (match uu____5249 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5279,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5315 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5315 with
        | (pfx,uu____5325) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5337 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5337 with
             | (uu____5344,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
    fun v1  ->
      fun v2  ->
        let as_set1 v3 =
          FStar_All.pipe_right v3
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set1 v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____5456 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5457 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5521  ->
                  fun uu____5522  ->
                    match (uu____5521, uu____5522) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5625 =
                          let uu____5626 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5626
                           in
                        if uu____5625
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5655 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5655
                           then
                             let uu____5670 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5670)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5457 with | (isect,uu____5719) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5754 'Auu____5755 .
    (FStar_Syntax_Syntax.bv,'Auu____5754) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5755) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5812  ->
              fun uu____5813  ->
                match (uu____5812, uu____5813) with
                | ((a,uu____5831),(b,uu____5833)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5848 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5848) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5878  ->
           match uu____5878 with
           | (y,uu____5884) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5893 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5893) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6055 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6055
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6085 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____6132 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6170 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6183 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___335_6188  ->
    match uu___335_6188 with
    | MisMatch (d1,d2) ->
        let uu____6199 =
          let uu____6200 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6201 =
            let uu____6202 =
              let uu____6203 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6203 ")"  in
            Prims.strcat ") (" uu____6202  in
          Prims.strcat uu____6200 uu____6201  in
        Prims.strcat "MisMatch (" uu____6199
    | HeadMatch u ->
        let uu____6205 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6205
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___336_6210  ->
    match uu___336_6210 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6225 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d1
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____6240 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6240 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6251 -> d)
      | d1 -> d1
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____6274 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6283 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6309 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6309
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6310 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6311 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6312 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6325 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6338 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6362) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6368,uu____6369) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6411) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6436;
             FStar_Syntax_Syntax.index = uu____6437;
             FStar_Syntax_Syntax.sort = t2;_},uu____6439)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6446 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6447 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6448 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6463 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6470 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6490 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6490
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____6508;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6509;
             FStar_Syntax_Syntax.ltyp = uu____6510;
             FStar_Syntax_Syntax.rng = uu____6511;_},uu____6512)
            ->
            let uu____6523 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____6523 t21
        | (uu____6524,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____6525;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6526;
             FStar_Syntax_Syntax.ltyp = uu____6527;
             FStar_Syntax_Syntax.rng = uu____6528;_})
            ->
            let uu____6539 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____6539
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6549 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6549
            then FullMatch
            else
              (let uu____6551 =
                 let uu____6560 =
                   let uu____6563 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6563  in
                 let uu____6564 =
                   let uu____6567 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6567  in
                 (uu____6560, uu____6564)  in
               MisMatch uu____6551)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6573),FStar_Syntax_Syntax.Tm_uinst (g,uu____6575)) ->
            let uu____6584 = head_matches env f g  in
            FStar_All.pipe_right uu____6584 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6587 = FStar_Const.eq_const c d  in
            if uu____6587
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6594),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6596)) ->
            let uu____6629 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6629
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6636),FStar_Syntax_Syntax.Tm_refine (y,uu____6638)) ->
            let uu____6647 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6647 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6649),uu____6650) ->
            let uu____6655 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6655 head_match
        | (uu____6656,FStar_Syntax_Syntax.Tm_refine (x,uu____6658)) ->
            let uu____6663 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6663 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6664,FStar_Syntax_Syntax.Tm_type
           uu____6665) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6666,FStar_Syntax_Syntax.Tm_arrow uu____6667) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6697),FStar_Syntax_Syntax.Tm_app (head',uu____6699))
            ->
            let uu____6748 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6748 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6750),uu____6751) ->
            let uu____6776 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6776 head_match
        | (uu____6777,FStar_Syntax_Syntax.Tm_app (head1,uu____6779)) ->
            let uu____6804 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6804 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6805,FStar_Syntax_Syntax.Tm_let
           uu____6806) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6831,FStar_Syntax_Syntax.Tm_match uu____6832) ->
            HeadMatch true
        | uu____6877 ->
            let uu____6882 =
              let uu____6891 = delta_depth_of_term env t11  in
              let uu____6894 = delta_depth_of_term env t21  in
              (uu____6891, uu____6894)  in
            MisMatch uu____6882
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                        FStar_Pervasives_Native.tuple2
                        FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let maybe_inline t =
          let head1 = FStar_Syntax_Util.head_of t  in
          (let uu____6954 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6954
           then
             let uu____6955 = FStar_Syntax_Print.term_to_string t  in
             let uu____6956 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____6955 uu____6956
           else ());
          (let uu____6958 =
             let uu____6959 = FStar_Syntax_Util.un_uinst head1  in
             uu____6959.FStar_Syntax_Syntax.n  in
           match uu____6958 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____6965 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____6965 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____6979 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____6979
                      then
                        let uu____6980 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____6980
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____6982 ->
                    let t' =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota] env t
                       in
                    ((let uu____6993 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____6993
                      then
                        let uu____6994 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____6995 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____6994
                          uu____6995
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____6997 -> FStar_Pervasives_Native.None)
           in
        let success d r t11 t21 =
          (r,
            (if d > (Prims.parse_int "0")
             then FStar_Pervasives_Native.Some (t11, t21)
             else FStar_Pervasives_Native.None))
           in
        let fail1 d r t11 t21 =
          (r,
            (if d > (Prims.parse_int "0")
             then FStar_Pervasives_Native.Some (t11, t21)
             else FStar_Pervasives_Native.None))
           in
        let rec aux retry n_delta t11 t21 =
          let r = head_matches env t11 t21  in
          (let uu____7135 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7135
           then
             let uu____7136 = FStar_Syntax_Print.term_to_string t11  in
             let uu____7137 = FStar_Syntax_Print.term_to_string t21  in
             let uu____7138 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7136
               uu____7137 uu____7138
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____7162 =
               if d1_greater_than_d2
               then
                 let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Env.UnfoldUntil d2;
                     FStar_TypeChecker_Env.Weak;
                     FStar_TypeChecker_Env.HNF] env t11
                    in
                 (t1', t21)
               else
                 (let t2' =
                    normalize_refinement
                      [FStar_TypeChecker_Env.UnfoldUntil d1;
                      FStar_TypeChecker_Env.Weak;
                      FStar_TypeChecker_Env.HNF] env t21
                     in
                  (t11, t2'))
                in
             match uu____7162 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____7207 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____7207 with
             | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
             | FStar_Pervasives_Native.Some d1 ->
                 let t12 =
                   normalize_refinement
                     [FStar_TypeChecker_Env.UnfoldUntil d1;
                     FStar_TypeChecker_Env.Weak;
                     FStar_TypeChecker_Env.HNF] env t11
                    in
                 let t22 =
                   normalize_refinement
                     [FStar_TypeChecker_Env.UnfoldUntil d1;
                     FStar_TypeChecker_Env.Weak;
                     FStar_TypeChecker_Env.HNF] env t21
                    in
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           match r with
           | MisMatch
               (FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level
                i),FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level j))
               when
               ((i > (Prims.parse_int "0")) || (j > (Prims.parse_int "0")))
                 && (i <> j)
               ->
               reduce_one_and_try_again
                 (FStar_Syntax_Syntax.Delta_equational_at_level i)
                 (FStar_Syntax_Syntax.Delta_equational_at_level j)
           | MisMatch
               (FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level
                uu____7239),uu____7240)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7258 =
                    let uu____7267 = maybe_inline t11  in
                    let uu____7270 = maybe_inline t21  in
                    (uu____7267, uu____7270)  in
                  match uu____7258 with
                  | (FStar_Pervasives_Native.None
                     ,FStar_Pervasives_Native.None ) ->
                      fail1 n_delta r t11 t21
                  | (FStar_Pervasives_Native.Some
                     t12,FStar_Pervasives_Native.None ) ->
                      aux false (n_delta + (Prims.parse_int "1")) t12 t21
                  | (FStar_Pervasives_Native.None
                     ,FStar_Pervasives_Native.Some t22) ->
                      aux false (n_delta + (Prims.parse_int "1")) t11 t22
                  | (FStar_Pervasives_Native.Some
                     t12,FStar_Pervasives_Native.Some t22) ->
                      aux false (n_delta + (Prims.parse_int "1")) t12 t22)
           | MisMatch
               (uu____7307,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____7308))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7326 =
                    let uu____7335 = maybe_inline t11  in
                    let uu____7338 = maybe_inline t21  in
                    (uu____7335, uu____7338)  in
                  match uu____7326 with
                  | (FStar_Pervasives_Native.None
                     ,FStar_Pervasives_Native.None ) ->
                      fail1 n_delta r t11 t21
                  | (FStar_Pervasives_Native.Some
                     t12,FStar_Pervasives_Native.None ) ->
                      aux false (n_delta + (Prims.parse_int "1")) t12 t21
                  | (FStar_Pervasives_Native.None
                     ,FStar_Pervasives_Native.Some t22) ->
                      aux false (n_delta + (Prims.parse_int "1")) t11 t22
                  | (FStar_Pervasives_Native.Some
                     t12,FStar_Pervasives_Native.Some t22) ->
                      aux false (n_delta + (Prims.parse_int "1")) t12 t22)
           | MisMatch
               (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                d2)
               when d1 = d2 -> reduce_both_and_try_again d1 r
           | MisMatch
               (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                d2)
               -> reduce_one_and_try_again d1 d2
           | MisMatch uu____7387 -> fail1 n_delta r t11 t21
           | uu____7396 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____7409 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____7409
         then
           let uu____7410 = FStar_Syntax_Print.term_to_string t1  in
           let uu____7411 = FStar_Syntax_Print.term_to_string t2  in
           let uu____7412 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____7419 =
             if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
             then "None"
             else
               (let uu____7431 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7431
                  (fun uu____7465  ->
                     match uu____7465 with
                     | (t11,t21) ->
                         let uu____7472 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7473 =
                           let uu____7474 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7474  in
                         Prims.strcat uu____7472 uu____7473))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____7410 uu____7411 uu____7412 uu____7419
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7486 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7486 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___337_7499  ->
    match uu___337_7499 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> (Prims.parse_int "0")
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> (Prims.parse_int "1")
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.parse_int "2")
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.parse_int "3")
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.parse_int "4")
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.parse_int "5")
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___358_7536 = p  in
      let uu____7539 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7540 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___358_7536.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7539;
        FStar_TypeChecker_Common.relation =
          (uu___358_7536.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7540;
        FStar_TypeChecker_Common.element =
          (uu___358_7536.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___358_7536.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___358_7536.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___358_7536.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___358_7536.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___358_7536.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7554 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7554
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7559 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7581 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7581 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7589 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7589 with
           | (lh,lhs_args) ->
               let uu____7636 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7636 with
                | (rh,rhs_args) ->
                    let uu____7683 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7696,FStar_Syntax_Syntax.Tm_uvar uu____7697)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7786 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7813,uu____7814)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7829,FStar_Syntax_Syntax.Tm_uvar uu____7830)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7845,FStar_Syntax_Syntax.Tm_arrow uu____7846)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___359_7876 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___359_7876.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___359_7876.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___359_7876.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___359_7876.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___359_7876.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___359_7876.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___359_7876.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___359_7876.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___359_7876.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7879,FStar_Syntax_Syntax.Tm_type uu____7880)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___359_7896 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___359_7896.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___359_7896.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___359_7896.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___359_7896.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___359_7896.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___359_7896.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___359_7896.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___359_7896.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___359_7896.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7899,FStar_Syntax_Syntax.Tm_uvar uu____7900)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___359_7916 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___359_7916.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___359_7916.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___359_7916.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___359_7916.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___359_7916.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___359_7916.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___359_7916.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___359_7916.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___359_7916.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7919,FStar_Syntax_Syntax.Tm_uvar uu____7920)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7935,uu____7936)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7951,FStar_Syntax_Syntax.Tm_uvar uu____7952)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7967,uu____7968) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7683 with
                     | (rank,tp1) ->
                         let uu____7981 =
                           FStar_All.pipe_right
                             (let uu___360_7985 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___360_7985.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___360_7985.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___360_7985.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___360_7985.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___360_7985.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___360_7985.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___360_7985.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___360_7985.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___360_7985.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____7981))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7991 =
            FStar_All.pipe_right
              (let uu___361_7995 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___361_7995.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___361_7995.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___361_7995.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___361_7995.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___361_7995.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___361_7995.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___361_7995.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___361_7995.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___361_7995.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7991)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8056 probs =
      match uu____8056 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8137 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8158 = rank wl.tcenv hd1  in
               (match uu____8158 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____8217 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8221 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8221)
                          in
                       if uu____8217
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____8289 = FStar_Syntax_Util.head_and_args t  in
          match uu____8289 with
          | (hd1,uu____8307) ->
              let uu____8332 =
                let uu____8333 = FStar_Syntax_Subst.compress hd1  in
                uu____8333.FStar_Syntax_Syntax.n  in
              (match uu____8332 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8337) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8371  ->
                           match uu____8371 with
                           | (y,uu____8379) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8401  ->
                                       match uu____8401 with
                                       | (x,uu____8409) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8414 -> false)
           in
        let uu____8415 = rank tcenv p  in
        match uu____8415 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8422 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8449 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8463 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8477 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____8529 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8529 with
                        | (k,uu____8535) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8545 -> false)))
            | uu____8546 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8598 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8604 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8604 = (Prims.parse_int "0")))
                           in
                        if uu____8598 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8620 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8626 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8626 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8620)
               in
            let uu____8627 = filter1 u12  in
            let uu____8630 = filter1 u22  in (uu____8627, uu____8630)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8659 = filter_out_common_univs us1 us2  in
                (match uu____8659 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8718 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8718 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8721 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8731 =
                          let uu____8732 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8733 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8732
                            uu____8733
                           in
                        UFailed uu____8731))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8757 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8757 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8783 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8783 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8786 ->
                let uu____8791 =
                  let uu____8792 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8793 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8792
                    uu____8793 msg
                   in
                UFailed uu____8791
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8794,uu____8795) ->
              let uu____8796 =
                let uu____8797 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8798 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8797 uu____8798
                 in
              failwith uu____8796
          | (FStar_Syntax_Syntax.U_unknown ,uu____8799) ->
              let uu____8800 =
                let uu____8801 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8802 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8801 uu____8802
                 in
              failwith uu____8800
          | (uu____8803,FStar_Syntax_Syntax.U_bvar uu____8804) ->
              let uu____8805 =
                let uu____8806 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8807 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8806 uu____8807
                 in
              failwith uu____8805
          | (uu____8808,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8809 =
                let uu____8810 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8811 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8810 uu____8811
                 in
              failwith uu____8809
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8835 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8835
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8849 = occurs_univ v1 u3  in
              if uu____8849
              then
                let uu____8850 =
                  let uu____8851 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8852 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8851 uu____8852
                   in
                try_umax_components u11 u21 uu____8850
              else
                (let uu____8854 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8854)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8866 = occurs_univ v1 u3  in
              if uu____8866
              then
                let uu____8867 =
                  let uu____8868 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8869 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8868 uu____8869
                   in
                try_umax_components u11 u21 uu____8867
              else
                (let uu____8871 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8871)
          | (FStar_Syntax_Syntax.U_max uu____8872,uu____8873) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8879 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8879
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8881,FStar_Syntax_Syntax.U_max uu____8882) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8888 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8888
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8890,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8891,FStar_Syntax_Syntax.U_name
             uu____8892) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8893) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8894) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8895,FStar_Syntax_Syntax.U_succ
             uu____8896) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8897,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____8997 = bc1  in
      match uu____8997 with
      | (bs1,mk_cod1) ->
          let uu____9041 = bc2  in
          (match uu____9041 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9152 = aux xs ys  in
                     (match uu____9152 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9235 =
                       let uu____9242 = mk_cod1 xs  in ([], uu____9242)  in
                     let uu____9245 =
                       let uu____9252 = mk_cod2 ys  in ([], uu____9252)  in
                     (uu____9235, uu____9245)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____9320 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9320 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9323 =
                    let uu____9324 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9324 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9323
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9329 = has_type_guard t1 t2  in (uu____9329, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9330 = has_type_guard t2 t1  in (uu____9330, wl)
  
let is_flex_pat :
  'Auu____9339 'Auu____9340 'Auu____9341 .
    ('Auu____9339,'Auu____9340,'Auu____9341 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___338_9354  ->
    match uu___338_9354 with
    | (uu____9363,uu____9364,[]) -> true
    | uu____9367 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9398 = f  in
      match uu____9398 with
      | (uu____9405,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9406;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9407;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9410;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9411;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9412;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9472  ->
                 match uu____9472 with
                 | (y,uu____9480) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9634 =
                  let uu____9649 =
                    let uu____9652 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9652  in
                  ((FStar_List.rev pat_binders), uu____9649)  in
                FStar_Pervasives_Native.Some uu____9634
            | (uu____9685,[]) ->
                let uu____9716 =
                  let uu____9731 =
                    let uu____9734 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9734  in
                  ((FStar_List.rev pat_binders), uu____9731)  in
                FStar_Pervasives_Native.Some uu____9716
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9825 =
                  let uu____9826 = FStar_Syntax_Subst.compress a  in
                  uu____9826.FStar_Syntax_Syntax.n  in
                (match uu____9825 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9846 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9846
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___362_9873 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___362_9873.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___362_9873.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9877 =
                            let uu____9878 =
                              let uu____9885 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9885)  in
                            FStar_Syntax_Syntax.NT uu____9878  in
                          [uu____9877]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___363_9901 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___363_9901.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___363_9901.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9902 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9942 =
                  let uu____9957 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9957  in
                (match uu____9942 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10032 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10065 ->
               let uu____10066 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10066 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10350 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10350
       then
         let uu____10351 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10351
       else ());
      (let uu____10353 = next_prob probs  in
       match uu____10353 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___364_10380 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___364_10380.wl_deferred);
               ctr = (uu___364_10380.ctr);
               defer_ok = (uu___364_10380.defer_ok);
               smt_ok = (uu___364_10380.smt_ok);
               tcenv = (uu___364_10380.tcenv);
               wl_implicits = (uu___364_10380.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10388 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10388
                 then
                   let uu____10389 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10389
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t' env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t' env
                           (let uu___365_10394 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___365_10394.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___365_10394.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___365_10394.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___365_10394.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___365_10394.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___365_10394.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___365_10394.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___365_10394.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___365_10394.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10416 ->
                let uu____10425 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10484  ->
                          match uu____10484 with
                          | (c,uu____10492,uu____10493) -> c < probs.ctr))
                   in
                (match uu____10425 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10534 =
                            let uu____10539 =
                              FStar_List.map
                                (fun uu____10554  ->
                                   match uu____10554 with
                                   | (uu____10565,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10539, (probs.wl_implicits))  in
                          Success uu____10534
                      | uu____10568 ->
                          let uu____10577 =
                            let uu___366_10578 = probs  in
                            let uu____10579 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10598  ->
                                      match uu____10598 with
                                      | (uu____10605,uu____10606,y) -> y))
                               in
                            {
                              attempting = uu____10579;
                              wl_deferred = rest;
                              ctr = (uu___366_10578.ctr);
                              defer_ok = (uu___366_10578.defer_ok);
                              smt_ok = (uu___366_10578.smt_ok);
                              tcenv = (uu___366_10578.tcenv);
                              wl_implicits = (uu___366_10578.wl_implicits)
                            }  in
                          solve env uu____10577))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____10613 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10613 with
            | USolved wl1 ->
                let uu____10615 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10615
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____10667 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10667 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10670 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10682;
                  FStar_Syntax_Syntax.vars = uu____10683;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10686;
                  FStar_Syntax_Syntax.vars = uu____10687;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10699,uu____10700) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10707,FStar_Syntax_Syntax.Tm_uinst uu____10708) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10715 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____10725 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10725
              then
                let uu____10726 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10726 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____10812 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10812 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10865 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10865
                then
                  let uu____10866 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10867 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10866 uu____10867
                else ());
               (let uu____10869 = head_matches_delta env1 t1 t2  in
                match uu____10869 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10914 = eq_prob t1 t2 wl2  in
                         (match uu____10914 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10935 ->
                         let uu____10944 = eq_prob t1 t2 wl2  in
                         (match uu____10944 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____10993 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11008 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11009 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11008, uu____11009)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11014 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11015 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11014, uu____11015)
                            in
                         (match uu____10993 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11046 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11046 with
                                | (t1_hd,t1_args) ->
                                    let uu____11091 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11091 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11155 =
                                              let uu____11162 =
                                                let uu____11173 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11173 :: t1_args  in
                                              let uu____11190 =
                                                let uu____11199 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11199 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11248  ->
                                                   fun uu____11249  ->
                                                     fun uu____11250  ->
                                                       match (uu____11248,
                                                               uu____11249,
                                                               uu____11250)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11300),
                                                          (a2,uu____11302))
                                                           ->
                                                           let uu____11339 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11339
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11162
                                                uu____11190
                                               in
                                            match uu____11155 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___367_11365 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___367_11365.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___367_11365.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11373 =
                                                  solve env1 wl'  in
                                                (match uu____11373 with
                                                 | Success (uu____11376,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___368_11380
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___368_11380.attempting);
                                                            wl_deferred =
                                                              (uu___368_11380.wl_deferred);
                                                            ctr =
                                                              (uu___368_11380.ctr);
                                                            defer_ok =
                                                              (uu___368_11380.defer_ok);
                                                            smt_ok =
                                                              (uu___368_11380.smt_ok);
                                                            tcenv =
                                                              (uu___368_11380.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11381 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11413 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11413 with
                                | (t1_base,p1_opt) ->
                                    let uu____11448 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11448 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11546 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11546
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
                                              in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi1),FStar_Pervasives_Native.Some
                                              (y,phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____11594 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11594
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____11624 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11624
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____11654 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11654
                                           | uu____11657 -> t_base  in
                                         let uu____11674 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11674 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11688 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11688, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11695 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11695 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11730 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11730 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11765 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11765
                                                         with
                                                         | (p,wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1
                                                                in
                                                             (t, [p], wl4))))))
                                 in
                              let uu____11789 = combine t11 t21 wl2  in
                              (match uu____11789 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11822 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11822
                                     then
                                       let uu____11823 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11823
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11862 ts1 =
               match uu____11862 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____11925 = pairwise out t wl2  in
                        (match uu____11925 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____11961 =
               let uu____11972 = FStar_List.hd ts  in (uu____11972, [], wl1)
                in
             let uu____11981 = FStar_List.tl ts  in
             aux uu____11961 uu____11981  in
           let uu____11988 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____11988 with
           | (this_flex,this_rigid) ->
               let uu____12012 =
                 let uu____12013 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12013.FStar_Syntax_Syntax.n  in
               (match uu____12012 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12038 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12038
                    then
                      let uu____12039 = destruct_flex_t this_flex wl  in
                      (match uu____12039 with
                       | (flex,wl1) ->
                           let uu____12046 = quasi_pattern env flex  in
                           (match uu____12046 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12064 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12064
                                  then
                                    let uu____12065 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12065
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12068 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___369_12071 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___369_12071.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___369_12071.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___369_12071.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___369_12071.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___369_12071.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___369_12071.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___369_12071.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___369_12071.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___369_12071.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12068)
                | uu____12072 ->
                    ((let uu____12074 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12074
                      then
                        let uu____12075 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12075
                      else ());
                     (let uu____12077 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12077 with
                      | (u,_args) ->
                          let uu____12120 =
                            let uu____12121 = FStar_Syntax_Subst.compress u
                               in
                            uu____12121.FStar_Syntax_Syntax.n  in
                          (match uu____12120 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12148 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12148 with
                                 | (u',uu____12166) ->
                                     let uu____12191 =
                                       let uu____12192 = whnf env u'  in
                                       uu____12192.FStar_Syntax_Syntax.n  in
                                     (match uu____12191 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12213 -> false)
                                  in
                               let uu____12214 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___339_12237  ->
                                         match uu___339_12237 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____12246 -> false)
                                         | uu____12249 -> false))
                                  in
                               (match uu____12214 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12263 = whnf env this_rigid
                                         in
                                      let uu____12264 =
                                        FStar_List.collect
                                          (fun uu___340_12270  ->
                                             match uu___340_12270 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12276 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12276]
                                             | uu____12278 -> [])
                                          bounds_probs
                                         in
                                      uu____12263 :: uu____12264  in
                                    let uu____12279 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12279 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12310 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12325 =
                                               let uu____12326 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12326.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12325 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12338 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12338)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12347 -> bound  in
                                           let uu____12348 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12348)  in
                                         (match uu____12310 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12377 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12377
                                                then
                                                  let wl'1 =
                                                    let uu___370_12379 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___370_12379.wl_deferred);
                                                      ctr =
                                                        (uu___370_12379.ctr);
                                                      defer_ok =
                                                        (uu___370_12379.defer_ok);
                                                      smt_ok =
                                                        (uu___370_12379.smt_ok);
                                                      tcenv =
                                                        (uu___370_12379.tcenv);
                                                      wl_implicits =
                                                        (uu___370_12379.wl_implicits)
                                                    }  in
                                                  let uu____12380 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12380
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12383 =
                                                  solve_t env eq_prob
                                                    (let uu___371_12385 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___371_12385.wl_deferred);
                                                       ctr =
                                                         (uu___371_12385.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___371_12385.smt_ok);
                                                       tcenv =
                                                         (uu___371_12385.tcenv);
                                                       wl_implicits =
                                                         (uu___371_12385.wl_implicits)
                                                     })
                                                   in
                                                match uu____12383 with
                                                | Success uu____12386 ->
                                                    let wl2 =
                                                      let uu___372_12392 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___372_12392.wl_deferred);
                                                        ctr =
                                                          (uu___372_12392.ctr);
                                                        defer_ok =
                                                          (uu___372_12392.defer_ok);
                                                        smt_ok =
                                                          (uu___372_12392.smt_ok);
                                                        tcenv =
                                                          (uu___372_12392.tcenv);
                                                        wl_implicits =
                                                          (uu___372_12392.wl_implicits)
                                                      }  in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g  ->
                                                           fun p  ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs
                                                       in
                                                    let wl3 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl2
                                                       in
                                                    let uu____12407 =
                                                      FStar_List.fold_left
                                                        (fun wl4  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl4) wl3
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl3)
                                                | Failed (p,msg) ->
                                                    ((let uu____12418 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12418
                                                      then
                                                        let uu____12419 =
                                                          let uu____12420 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12420
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12419
                                                      else ());
                                                     (let uu____12426 =
                                                        let uu____12441 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12441)
                                                         in
                                                      match uu____12426 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12463))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12489 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12489
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join3"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2
                                                                     in
                                                                  let uu____12506
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12506))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12531 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12531
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi  in
                                                                  let wl3 =
                                                                    let uu____12549
                                                                    =
                                                                    let uu____12554
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12554
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12549
                                                                    [] wl2
                                                                     in
                                                                  let uu____12559
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12559))))
                                                      | uu____12560 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12575 when flip ->
                               let uu____12576 =
                                 let uu____12577 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12578 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12577 uu____12578
                                  in
                               failwith uu____12576
                           | uu____12579 ->
                               let uu____12580 =
                                 let uu____12581 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12582 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12581 uu____12582
                                  in
                               failwith uu____12580)))))

and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____12616  ->
                         match uu____12616 with
                         | (x,i) ->
                             let uu____12635 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12635, i)) bs_lhs
                     in
                  let uu____12638 = lhs  in
                  match uu____12638 with
                  | (uu____12639,u_lhs,uu____12641) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12738 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12748 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12748, univ)
                             in
                          match uu____12738 with
                          | (k,univ) ->
                              let uu____12755 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12755 with
                               | (uu____12772,u,wl3) ->
                                   let uu____12775 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12775, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12801 =
                              let uu____12814 =
                                let uu____12825 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12825 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12876  ->
                                   fun uu____12877  ->
                                     match (uu____12876, uu____12877) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12978 =
                                           let uu____12985 =
                                             let uu____12988 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12988
                                              in
                                           copy_uvar u_lhs [] uu____12985 wl2
                                            in
                                         (match uu____12978 with
                                          | (uu____13017,t_a,wl3) ->
                                              let uu____13020 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13020 with
                                               | (uu____13039,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12814
                                ([], wl1)
                               in
                            (match uu____12801 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___373_13095 = ct  in
                                   let uu____13096 =
                                     let uu____13099 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13099
                                      in
                                   let uu____13114 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___373_13095.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___373_13095.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13096;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13114;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___373_13095.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___374_13132 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___374_13132.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___374_13132.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13135 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13135 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13197 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13197 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13208 =
                                          let uu____13213 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13213)  in
                                        TERM uu____13208  in
                                      let uu____13214 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13214 with
                                       | (sub_prob,wl3) ->
                                           let uu____13227 =
                                             let uu____13228 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13228
                                              in
                                           solve env uu____13227))
                             | (x,imp)::formals2 ->
                                 let uu____13250 =
                                   let uu____13257 =
                                     let uu____13260 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13260
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13257 wl1
                                    in
                                 (match uu____13250 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13281 =
                                          let uu____13284 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13284
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13281 u_x
                                         in
                                      let uu____13285 =
                                        let uu____13288 =
                                          let uu____13291 =
                                            let uu____13292 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13292, imp)  in
                                          [uu____13291]  in
                                        FStar_List.append bs_terms
                                          uu____13288
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13285 formals2 wl2)
                              in
                           let uu____13319 = occurs_check u_lhs arrow1  in
                           (match uu____13319 with
                            | (uu____13330,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13341 =
                                    let uu____13342 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13342
                                     in
                                  giveup_or_defer env orig wl uu____13341
                                else aux [] [] formals wl))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob,worklist)
                       FStar_Pervasives_Native.tuple2)
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____13371 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13371
               then
                 let uu____13372 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13373 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13372 (rel_to_string (p_rel orig)) uu____13373
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13494 = rhs wl1 scope env1 subst1  in
                     (match uu____13494 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13514 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13514
                            then
                              let uu____13515 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13515
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13588 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13588 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___375_13590 = hd1  in
                       let uu____13591 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___375_13590.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___375_13590.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13591
                       }  in
                     let hd21 =
                       let uu___376_13595 = hd2  in
                       let uu____13596 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___376_13595.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___376_13595.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13596
                       }  in
                     let uu____13599 =
                       let uu____13604 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13604
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13599 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13623 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13623
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13627 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13627 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13690 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13690
                                  in
                               ((let uu____13708 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13708
                                 then
                                   let uu____13709 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13710 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13709
                                     uu____13710
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13737 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13770 = aux wl [] env [] bs1 bs2  in
               match uu____13770 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13819 = attempt sub_probs wl2  in
                   solve env uu____13819)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13824 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13824 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let binders_as_bv_set bs =
              let uu____13838 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13838 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13872 = lhs1  in
              match uu____13872 with
              | (uu____13875,ctx_u,uu____13877) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13885 ->
                        let uu____13886 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13886 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13933 = quasi_pattern env1 lhs1  in
              match uu____13933 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13963) ->
                  let uu____13968 = lhs1  in
                  (match uu____13968 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13982 = occurs_check ctx_u rhs1  in
                       (match uu____13982 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14024 =
                                let uu____14031 =
                                  let uu____14032 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14032
                                   in
                                FStar_Util.Inl uu____14031  in
                              (uu____14024, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14054 =
                                 let uu____14055 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14055  in
                               if uu____14054
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14075 =
                                    let uu____14082 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14082  in
                                  let uu____14087 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14075, uu____14087)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____14130 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14130 with
              | (rhs_hd,args) ->
                  let uu____14173 = FStar_Util.prefix args  in
                  (match uu____14173 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14245 = lhs1  in
                       (match uu____14245 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14249 =
                              let uu____14260 =
                                let uu____14267 =
                                  let uu____14270 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14270
                                   in
                                copy_uvar u_lhs [] uu____14267 wl1  in
                              match uu____14260 with
                              | (uu____14297,t_last_arg,wl2) ->
                                  let uu____14300 =
                                    let uu____14307 =
                                      let uu____14308 =
                                        let uu____14317 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14317]  in
                                      FStar_List.append bs_lhs uu____14308
                                       in
                                    copy_uvar u_lhs uu____14307 t_res_lhs wl2
                                     in
                                  (match uu____14300 with
                                   | (uu____14352,lhs',wl3) ->
                                       let uu____14355 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14355 with
                                        | (uu____14372,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14249 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14393 =
                                     let uu____14394 =
                                       let uu____14399 =
                                         let uu____14400 =
                                           let uu____14403 =
                                             let uu____14408 =
                                               let uu____14409 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14409]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14408
                                              in
                                           uu____14403
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14400
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14399)  in
                                     TERM uu____14394  in
                                   [uu____14393]  in
                                 let uu____14436 =
                                   let uu____14443 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14443 with
                                   | (p1,wl3) ->
                                       let uu____14462 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14462 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14436 with
                                  | (sub_probs,wl3) ->
                                      let uu____14493 =
                                        let uu____14494 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14494  in
                                      solve env1 uu____14493))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14527 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14527 with
                | (uu____14544,args) ->
                    (match args with | [] -> false | uu____14578 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14595 =
                  let uu____14596 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14596.FStar_Syntax_Syntax.n  in
                match uu____14595 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14599 -> true
                | uu____14614 -> false  in
              let uu____14615 = quasi_pattern env1 lhs1  in
              match uu____14615 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14626 =
                    let uu____14627 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14627
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14626
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14634 = is_app rhs1  in
                  if uu____14634
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14636 = is_arrow rhs1  in
                     if uu____14636
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14638 =
                          let uu____14639 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14639
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14638))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____14642 = lhs  in
                (match uu____14642 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14646 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14646 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14663 =
                              let uu____14666 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14666
                               in
                            FStar_All.pipe_right uu____14663
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14683 = occurs_check ctx_uv rhs1  in
                          (match uu____14683 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14705 =
                                   let uu____14706 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14706
                                    in
                                 giveup_or_defer env orig wl uu____14705
                               else
                                 (let uu____14708 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14708
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14713 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14713
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14715 =
                                         let uu____14716 =
                                           names_to_string1 fvs2  in
                                         let uu____14717 =
                                           names_to_string1 fvs1  in
                                         let uu____14718 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14716 uu____14717
                                           uu____14718
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14715)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14726 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14730 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14730 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14753 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14753
                             | (FStar_Util.Inl msg,uu____14755) ->
                                 first_order orig env wl lhs rhs)))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then giveup_or_defer env orig wl "flex-flex non-pattern"
                else
                  (let uu____14788 =
                     let uu____14805 = quasi_pattern env lhs  in
                     let uu____14812 = quasi_pattern env rhs  in
                     (uu____14805, uu____14812)  in
                   match uu____14788 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14855 = lhs  in
                       (match uu____14855 with
                        | ({ FStar_Syntax_Syntax.n = uu____14856;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14858;_},u_lhs,uu____14860)
                            ->
                            let uu____14863 = rhs  in
                            (match uu____14863 with
                             | (uu____14864,u_rhs,uu____14866) ->
                                 let uu____14867 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14867
                                 then
                                   let uu____14872 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14872
                                 else
                                   (let uu____14874 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____14874 with
                                    | (ctx_w,(ctx_l,ctx_r)) ->
                                        let gamma_w =
                                          gamma_until
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                            ctx_w
                                           in
                                        let zs =
                                          intersect_binders gamma_w
                                            (FStar_List.append ctx_l
                                               binders_lhs)
                                            (FStar_List.append ctx_r
                                               binders_rhs)
                                           in
                                        let uu____14906 =
                                          let uu____14913 =
                                            let uu____14916 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____14916
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____14913
                                            FStar_Syntax_Syntax.Strict
                                           in
                                        (match uu____14906 with
                                         | (uu____14919,w,wl1) ->
                                             let w_app =
                                               let uu____14925 =
                                                 let uu____14930 =
                                                   FStar_List.map
                                                     (fun uu____14941  ->
                                                        match uu____14941
                                                        with
                                                        | (z,uu____14949) ->
                                                            let uu____14954 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____14954) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____14930
                                                  in
                                               uu____14925
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____14958 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____14958
                                               then
                                                 let uu____14959 =
                                                   let uu____14962 =
                                                     flex_t_to_string lhs  in
                                                   let uu____14963 =
                                                     let uu____14966 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____14967 =
                                                       let uu____14970 =
                                                         term_to_string w  in
                                                       let uu____14971 =
                                                         let uu____14974 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____14981 =
                                                           let uu____14984 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____14991 =
                                                             let uu____14994
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____14994]
                                                              in
                                                           uu____14984 ::
                                                             uu____14991
                                                            in
                                                         uu____14974 ::
                                                           uu____14981
                                                          in
                                                       uu____14970 ::
                                                         uu____14971
                                                        in
                                                     uu____14966 ::
                                                       uu____14967
                                                      in
                                                   uu____14962 :: uu____14963
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____14959
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____15000 =
                                                     let uu____15005 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____15005)  in
                                                   TERM uu____15000  in
                                                 let uu____15006 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____15006
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____15011 =
                                                        let uu____15016 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____15016)
                                                         in
                                                      TERM uu____15011  in
                                                    [s1; s2])
                                                  in
                                               let uu____15017 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____15017))))))
                   | uu____15018 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____15082 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15082
            then
              let uu____15083 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15084 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15085 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15086 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15083 uu____15084 uu____15085 uu____15086
            else ());
           (let uu____15089 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15089 with
            | (head1,args1) ->
                let uu____15132 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15132 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15196 =
                         let uu____15197 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15198 = args_to_string args1  in
                         let uu____15201 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15202 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15197 uu____15198 uu____15201 uu____15202
                          in
                       giveup env1 uu____15196 orig
                     else
                       (let uu____15206 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15212 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15212 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15206
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___377_15214 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___377_15214.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___377_15214.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___377_15214.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___377_15214.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___377_15214.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___377_15214.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___377_15214.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___377_15214.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____15216 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____15216 with
                              | USolved wl2 ->
                                  let uu____15218 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____15218
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____15222 = base_and_refinement env1 t1  in
                           match uu____15222 with
                           | (base1,refinement1) ->
                               let uu____15247 = base_and_refinement env1 t2
                                  in
                               (match uu____15247 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         if need_unif
                                         then
                                           let argp =
                                             FStar_List.zip
                                               ((head1,
                                                  FStar_Pervasives_Native.None)
                                               :: args1)
                                               ((head2,
                                                  FStar_Pervasives_Native.None)
                                               :: args2)
                                              in
                                           let uu____15367 =
                                             FStar_List.fold_right
                                               (fun uu____15407  ->
                                                  fun uu____15408  ->
                                                    match (uu____15407,
                                                            uu____15408)
                                                    with
                                                    | (((a1,uu____15460),
                                                        (a2,uu____15462)),
                                                       (probs,wl2)) ->
                                                        let uu____15511 =
                                                          let uu____15518 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____15518 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15511
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____15367 with
                                            | (subprobs,wl2) ->
                                                ((let uu____15550 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____15550
                                                  then
                                                    let uu____15551 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____15551
                                                  else ());
                                                 (let formula =
                                                    let uu____15556 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____15556
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____15564 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____15564)))
                                         else
                                           (let uu____15566 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____15566 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____15570 =
                                                  FStar_List.fold_right2
                                                    (fun uu____15607  ->
                                                       fun uu____15608  ->
                                                         fun uu____15609  ->
                                                           match (uu____15607,
                                                                   uu____15608,
                                                                   uu____15609)
                                                           with
                                                           | ((a,uu____15653),
                                                              (a',uu____15655),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____15688
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____15688
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____15570 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____15718 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____15718
                                                       then
                                                         let uu____15719 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____15719
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____15725 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____15725
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____15733 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____15733))))
                                     | uu____15734 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___378_15770 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___378_15770.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___378_15770.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___378_15770.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___378_15770.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___378_15770.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___378_15770.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___378_15770.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___378_15770.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____15845 = destruct_flex_t scrutinee wl1  in
             match uu____15845 with
             | ((_t,uv,_args),wl2) ->
                 let uu____15856 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____15856 with
                  | (xs,pat_term,uu____15871,uu____15872) ->
                      let uu____15877 =
                        FStar_List.fold_left
                          (fun uu____15900  ->
                             fun x  ->
                               match uu____15900 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____15921 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____15921 with
                                    | (uu____15940,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____15877 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____15961 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____15961 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___379_15977 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___379_15977.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___379_15977.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____15985 = solve env1 wl'  in
                                (match uu____15985 with
                                 | Success (uu____15988,imps) ->
                                     let wl'1 =
                                       let uu___380_15991 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___380_15991.wl_deferred);
                                         ctr = (uu___380_15991.ctr);
                                         defer_ok = (uu___380_15991.defer_ok);
                                         smt_ok = (uu___380_15991.smt_ok);
                                         tcenv = (uu___380_15991.tcenv);
                                         wl_implicits =
                                           (uu___380_15991.wl_implicits)
                                       }  in
                                     let uu____15992 = solve env1 wl'1  in
                                     (match uu____15992 with
                                      | Success (uu____15995,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___381_15999 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___381_15999.attempting);
                                                 wl_deferred =
                                                   (uu___381_15999.wl_deferred);
                                                 ctr = (uu___381_15999.ctr);
                                                 defer_ok =
                                                   (uu___381_15999.defer_ok);
                                                 smt_ok =
                                                   (uu___381_15999.smt_ok);
                                                 tcenv =
                                                   (uu___381_15999.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16000 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16006 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16027 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16027
                 then
                   let uu____16028 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16029 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16028 uu____16029
                 else ());
                (let uu____16031 =
                   let uu____16052 =
                     let uu____16061 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16061)  in
                   let uu____16068 =
                     let uu____16077 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16077)  in
                   (uu____16052, uu____16068)  in
                 match uu____16031 with
                 | ((uu____16106,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16109;
                                   FStar_Syntax_Syntax.vars = uu____16110;_}),
                    (s,t)) ->
                     let uu____16181 =
                       let uu____16182 = is_flex scrutinee  in
                       Prims.op_Negation uu____16182  in
                     if uu____16181
                     then
                       ((let uu____16190 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16190
                         then
                           let uu____16191 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16191
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16203 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16203
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16209 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16209
                           then
                             let uu____16210 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16211 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16210 uu____16211
                           else ());
                          (let pat_discriminates uu___341_16232 =
                             match uu___341_16232 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16247;
                                  FStar_Syntax_Syntax.p = uu____16248;_},FStar_Pervasives_Native.None
                                ,uu____16249) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16262;
                                  FStar_Syntax_Syntax.p = uu____16263;_},FStar_Pervasives_Native.None
                                ,uu____16264) -> true
                             | uu____16289 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16389 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16389 with
                                       | (uu____16390,uu____16391,t') ->
                                           let uu____16409 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16409 with
                                            | (FullMatch ,uu____16420) ->
                                                true
                                            | (HeadMatch
                                               uu____16433,uu____16434) ->
                                                true
                                            | uu____16447 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16480 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16480
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16485 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16485 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16573,uu____16574) ->
                                       branches1
                                   | uu____16719 -> branches  in
                                 let uu____16774 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____16783 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____16783 with
                                        | (p,uu____16787,uu____16788) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____16774))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____16844 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____16844 with
                                | (p,uu____16852,e) ->
                                    ((let uu____16871 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____16871
                                      then
                                        let uu____16872 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____16873 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____16872 uu____16873
                                      else ());
                                     (let uu____16875 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____16875)))))
                 | ((s,t),(uu____16890,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____16893;
                                         FStar_Syntax_Syntax.vars =
                                           uu____16894;_}))
                     ->
                     let uu____16963 =
                       let uu____16964 = is_flex scrutinee  in
                       Prims.op_Negation uu____16964  in
                     if uu____16963
                     then
                       ((let uu____16972 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16972
                         then
                           let uu____16973 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16973
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16985 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16985
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16991 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16991
                           then
                             let uu____16992 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16993 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16992 uu____16993
                           else ());
                          (let pat_discriminates uu___341_17014 =
                             match uu___341_17014 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17029;
                                  FStar_Syntax_Syntax.p = uu____17030;_},FStar_Pervasives_Native.None
                                ,uu____17031) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17044;
                                  FStar_Syntax_Syntax.p = uu____17045;_},FStar_Pervasives_Native.None
                                ,uu____17046) -> true
                             | uu____17071 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17171 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17171 with
                                       | (uu____17172,uu____17173,t') ->
                                           let uu____17191 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____17191 with
                                            | (FullMatch ,uu____17202) ->
                                                true
                                            | (HeadMatch
                                               uu____17215,uu____17216) ->
                                                true
                                            | uu____17229 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17262 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17262
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17267 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17267 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17355,uu____17356) ->
                                       branches1
                                   | uu____17501 -> branches  in
                                 let uu____17556 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17565 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17565 with
                                        | (p,uu____17569,uu____17570) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17556))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17626 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17626 with
                                | (p,uu____17634,e) ->
                                    ((let uu____17653 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17653
                                      then
                                        let uu____17654 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17655 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17654 uu____17655
                                      else ());
                                     (let uu____17657 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17657)))))
                 | uu____17670 ->
                     ((let uu____17692 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17692
                       then
                         let uu____17693 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17694 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17693 uu____17694
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____17735 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____17735
            then
              let uu____17736 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17737 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____17738 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17739 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____17736 uu____17737 uu____17738 uu____17739
            else ());
           (let uu____17741 = head_matches_delta env1 t1 t2  in
            match uu____17741 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____17772,uu____17773) ->
                     let rec may_relate head3 =
                       let uu____17800 =
                         let uu____17801 = FStar_Syntax_Subst.compress head3
                            in
                         uu____17801.FStar_Syntax_Syntax.n  in
                       match uu____17800 with
                       | FStar_Syntax_Syntax.Tm_name uu____17804 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____17805 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____17829 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____17829 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____17830 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____17831
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____17832 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____17834,uu____17835) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____17877) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____17883) ->
                           may_relate t
                       | uu____17888 -> false  in
                     let uu____17889 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____17889 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____17904 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____17904
                          then
                            let uu____17905 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____17905 with
                             | (guard,wl2) ->
                                 let uu____17912 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____17912)
                          else
                            (let uu____17914 =
                               let uu____17915 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____17916 =
                                 let uu____17917 =
                                   let uu____17920 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____17920
                                     (fun x  ->
                                        let uu____17926 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____17926)
                                    in
                                 FStar_Util.dflt "" uu____17917  in
                               let uu____17927 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____17928 =
                                 let uu____17929 =
                                   let uu____17932 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____17932
                                     (fun x  ->
                                        let uu____17938 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____17938)
                                    in
                                 FStar_Util.dflt "" uu____17929  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____17915 uu____17916 uu____17927
                                 uu____17928
                                in
                             giveup env1 uu____17914 orig))
                 | (HeadMatch (true ),uu____17939) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____17952 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____17952 with
                        | (guard,wl2) ->
                            let uu____17959 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____17959)
                     else
                       (let uu____17961 =
                          let uu____17962 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____17963 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____17962 uu____17963
                           in
                        giveup env1 uu____17961 orig)
                 | (uu____17964,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___382_17978 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___382_17978.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___382_17978.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___382_17978.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___382_17978.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___382_17978.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___382_17978.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___382_17978.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___382_17978.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18002 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18002
          then
            let uu____18003 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18003
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18008 =
                let uu____18011 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18011  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18008 t1);
             (let uu____18029 =
                let uu____18032 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18032  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18029 t2);
             (let uu____18050 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18050
              then
                let uu____18051 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18052 =
                  let uu____18053 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18054 =
                    let uu____18055 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18055  in
                  Prims.strcat uu____18053 uu____18054  in
                let uu____18056 =
                  let uu____18057 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18058 =
                    let uu____18059 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18059  in
                  Prims.strcat uu____18057 uu____18058  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18051
                  uu____18052 uu____18056
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18062,uu____18063) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18086,FStar_Syntax_Syntax.Tm_delayed uu____18087) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18110,uu____18111) ->
                  let uu____18138 =
                    let uu___383_18139 = problem  in
                    let uu____18140 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___383_18139.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18140;
                      FStar_TypeChecker_Common.relation =
                        (uu___383_18139.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___383_18139.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___383_18139.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___383_18139.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___383_18139.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___383_18139.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___383_18139.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___383_18139.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18138 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18141,uu____18142) ->
                  let uu____18149 =
                    let uu___384_18150 = problem  in
                    let uu____18151 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___384_18150.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18151;
                      FStar_TypeChecker_Common.relation =
                        (uu___384_18150.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___384_18150.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___384_18150.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___384_18150.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___384_18150.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___384_18150.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___384_18150.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___384_18150.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18149 wl
              | (uu____18152,FStar_Syntax_Syntax.Tm_ascribed uu____18153) ->
                  let uu____18180 =
                    let uu___385_18181 = problem  in
                    let uu____18182 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___385_18181.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___385_18181.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___385_18181.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18182;
                      FStar_TypeChecker_Common.element =
                        (uu___385_18181.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___385_18181.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___385_18181.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___385_18181.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___385_18181.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___385_18181.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18180 wl
              | (uu____18183,FStar_Syntax_Syntax.Tm_meta uu____18184) ->
                  let uu____18191 =
                    let uu___386_18192 = problem  in
                    let uu____18193 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___386_18192.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___386_18192.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___386_18192.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18193;
                      FStar_TypeChecker_Common.element =
                        (uu___386_18192.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___386_18192.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___386_18192.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___386_18192.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___386_18192.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___386_18192.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18191 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18195),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18197)) ->
                  let uu____18206 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18206
              | (FStar_Syntax_Syntax.Tm_bvar uu____18207,uu____18208) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18209,FStar_Syntax_Syntax.Tm_bvar uu____18210) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___342_18279 =
                    match uu___342_18279 with
                    | [] -> c
                    | bs ->
                        let uu____18307 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18307
                     in
                  let uu____18318 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18318 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____18467 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18467
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___343_18552 =
                    match uu___343_18552 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18594 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18594 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____18739 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18740 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____18739
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18740 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____18741,uu____18742) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18771 -> true
                    | uu____18790 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____18843 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_18851 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_18851.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_18851.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_18851.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_18851.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_18851.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_18851.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_18851.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_18851.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_18851.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_18851.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_18851.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_18851.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_18851.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_18851.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_18851.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_18851.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_18851.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_18851.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_18851.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_18851.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_18851.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_18851.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_18851.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_18851.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_18851.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_18851.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_18851.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_18851.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_18851.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_18851.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___387_18851.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_18851.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_18851.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_18851.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_18851.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_18851.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_18851.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_18851.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_18851.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____18843 with
                       | (uu____18854,ty,uu____18856) ->
                           let uu____18857 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____18857)
                     in
                  let uu____18858 =
                    let uu____18875 = maybe_eta t1  in
                    let uu____18882 = maybe_eta t2  in
                    (uu____18875, uu____18882)  in
                  (match uu____18858 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_18924 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_18924.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_18924.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_18924.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_18924.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_18924.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_18924.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_18924.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_18924.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____18945 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18945
                       then
                         let uu____18946 = destruct_flex_t not_abs wl  in
                         (match uu____18946 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_18961 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_18961.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_18961.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_18961.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_18961.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_18961.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_18961.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_18961.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_18961.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____18983 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18983
                       then
                         let uu____18984 = destruct_flex_t not_abs wl  in
                         (match uu____18984 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_18999 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_18999.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_18999.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_18999.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_18999.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_18999.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_18999.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_18999.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_18999.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19001 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19018,FStar_Syntax_Syntax.Tm_abs uu____19019) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19048 -> true
                    | uu____19067 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____19120 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19128 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19128.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19128.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19128.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19128.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19128.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19128.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19128.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19128.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19128.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19128.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19128.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19128.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19128.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19128.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19128.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19128.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19128.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19128.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19128.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19128.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19128.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19128.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19128.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19128.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19128.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19128.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19128.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19128.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19128.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19128.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___387_19128.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19128.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19128.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19128.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19128.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19128.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19128.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19128.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19128.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19120 with
                       | (uu____19131,ty,uu____19133) ->
                           let uu____19134 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19134)
                     in
                  let uu____19135 =
                    let uu____19152 = maybe_eta t1  in
                    let uu____19159 = maybe_eta t2  in
                    (uu____19152, uu____19159)  in
                  (match uu____19135 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19201 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19201.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19201.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19201.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19201.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19201.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19201.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19201.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19201.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19222 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19222
                       then
                         let uu____19223 = destruct_flex_t not_abs wl  in
                         (match uu____19223 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19238 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19238.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19238.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19238.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19238.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19238.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19238.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19238.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19238.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19260 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19260
                       then
                         let uu____19261 = destruct_flex_t not_abs wl  in
                         (match uu____19261 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19276 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19276.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19276.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19276.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19276.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19276.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19276.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19276.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19276.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19278 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19307 =
                    let uu____19312 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19312 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___390_19340 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19340.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19340.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19342 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19342.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19342.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19343,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___390_19357 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19357.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19357.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19359 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19359.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19359.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19360 -> (x1, x2)  in
                  (match uu____19307 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19379 = as_refinement false env t11  in
                       (match uu____19379 with
                        | (x12,phi11) ->
                            let uu____19386 = as_refinement false env t21  in
                            (match uu____19386 with
                             | (x22,phi21) ->
                                 ((let uu____19394 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19394
                                   then
                                     ((let uu____19396 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19397 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19398 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19396
                                         uu____19397 uu____19398);
                                      (let uu____19399 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19400 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19401 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19399
                                         uu____19400 uu____19401))
                                   else ());
                                  (let uu____19403 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19403 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            ((Prims.parse_int "0"), x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp1 imp phi13 phi23 =
                                         let uu____19471 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19471
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19483 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp1 FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp1 FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____19494 =
                                            let uu____19497 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19497
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19494
                                            (p_guard base_prob));
                                         (let uu____19515 =
                                            let uu____19518 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19518
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19515
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19536 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19536)
                                          in
                                       let has_uvars =
                                         (let uu____19540 =
                                            let uu____19541 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19541
                                             in
                                          Prims.op_Negation uu____19540) ||
                                           (let uu____19545 =
                                              let uu____19546 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19546
                                               in
                                            Prims.op_Negation uu____19545)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19549 =
                                           let uu____19554 =
                                             let uu____19563 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19563]  in
                                           mk_t_problem wl1 uu____19554 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19549 with
                                          | (ref_prob,wl2) ->
                                              let uu____19584 =
                                                solve env1
                                                  (let uu___392_19586 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___392_19586.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___392_19586.smt_ok);
                                                     tcenv =
                                                       (uu___392_19586.tcenv);
                                                     wl_implicits =
                                                       (uu___392_19586.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19584 with
                                               | Failed (prob,msg) ->
                                                   if
                                                     ((Prims.op_Negation
                                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                        && has_uvars)
                                                       ||
                                                       (Prims.op_Negation
                                                          wl2.smt_ok)
                                                   then giveup env1 msg prob
                                                   else fallback ()
                                               | Success uu____19596 ->
                                                   let guard =
                                                     let uu____19604 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19604
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___393_19613 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___393_19613.attempting);
                                                       wl_deferred =
                                                         (uu___393_19613.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___393_19613.defer_ok);
                                                       smt_ok =
                                                         (uu___393_19613.smt_ok);
                                                       tcenv =
                                                         (uu___393_19613.tcenv);
                                                       wl_implicits =
                                                         (uu___393_19613.wl_implicits)
                                                     }  in
                                                   let uu____19614 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19614))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19616,FStar_Syntax_Syntax.Tm_uvar uu____19617) ->
                  let uu____19642 = destruct_flex_t t1 wl  in
                  (match uu____19642 with
                   | (f1,wl1) ->
                       let uu____19649 = destruct_flex_t t2 wl1  in
                       (match uu____19649 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19656;
                    FStar_Syntax_Syntax.pos = uu____19657;
                    FStar_Syntax_Syntax.vars = uu____19658;_},uu____19659),FStar_Syntax_Syntax.Tm_uvar
                 uu____19660) ->
                  let uu____19709 = destruct_flex_t t1 wl  in
                  (match uu____19709 with
                   | (f1,wl1) ->
                       let uu____19716 = destruct_flex_t t2 wl1  in
                       (match uu____19716 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19723,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19724;
                    FStar_Syntax_Syntax.pos = uu____19725;
                    FStar_Syntax_Syntax.vars = uu____19726;_},uu____19727))
                  ->
                  let uu____19776 = destruct_flex_t t1 wl  in
                  (match uu____19776 with
                   | (f1,wl1) ->
                       let uu____19783 = destruct_flex_t t2 wl1  in
                       (match uu____19783 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19790;
                    FStar_Syntax_Syntax.pos = uu____19791;
                    FStar_Syntax_Syntax.vars = uu____19792;_},uu____19793),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19794;
                    FStar_Syntax_Syntax.pos = uu____19795;
                    FStar_Syntax_Syntax.vars = uu____19796;_},uu____19797))
                  ->
                  let uu____19870 = destruct_flex_t t1 wl  in
                  (match uu____19870 with
                   | (f1,wl1) ->
                       let uu____19877 = destruct_flex_t t2 wl1  in
                       (match uu____19877 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____19884,uu____19885) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____19898 = destruct_flex_t t1 wl  in
                  (match uu____19898 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19905;
                    FStar_Syntax_Syntax.pos = uu____19906;
                    FStar_Syntax_Syntax.vars = uu____19907;_},uu____19908),uu____19909)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____19946 = destruct_flex_t t1 wl  in
                  (match uu____19946 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____19953,FStar_Syntax_Syntax.Tm_uvar uu____19954) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____19967,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19968;
                    FStar_Syntax_Syntax.pos = uu____19969;
                    FStar_Syntax_Syntax.vars = uu____19970;_},uu____19971))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20008,FStar_Syntax_Syntax.Tm_arrow uu____20009) ->
                  solve_t' env
                    (let uu___394_20037 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20037.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20037.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20037.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20037.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20037.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20037.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20037.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20037.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20037.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20038;
                    FStar_Syntax_Syntax.pos = uu____20039;
                    FStar_Syntax_Syntax.vars = uu____20040;_},uu____20041),FStar_Syntax_Syntax.Tm_arrow
                 uu____20042) ->
                  solve_t' env
                    (let uu___394_20094 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20094.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20094.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20094.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20094.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20094.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20094.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20094.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20094.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20094.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20095,FStar_Syntax_Syntax.Tm_uvar uu____20096) ->
                  let uu____20109 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20109
              | (uu____20110,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20111;
                    FStar_Syntax_Syntax.pos = uu____20112;
                    FStar_Syntax_Syntax.vars = uu____20113;_},uu____20114))
                  ->
                  let uu____20151 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20151
              | (FStar_Syntax_Syntax.Tm_uvar uu____20152,uu____20153) ->
                  let uu____20166 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20166
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20167;
                    FStar_Syntax_Syntax.pos = uu____20168;
                    FStar_Syntax_Syntax.vars = uu____20169;_},uu____20170),uu____20171)
                  ->
                  let uu____20208 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20208
              | (FStar_Syntax_Syntax.Tm_refine uu____20209,uu____20210) ->
                  let t21 =
                    let uu____20218 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20218  in
                  solve_t env
                    (let uu___395_20244 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___395_20244.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___395_20244.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___395_20244.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___395_20244.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___395_20244.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___395_20244.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___395_20244.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___395_20244.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___395_20244.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20245,FStar_Syntax_Syntax.Tm_refine uu____20246) ->
                  let t11 =
                    let uu____20254 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20254  in
                  solve_t env
                    (let uu___396_20280 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___396_20280.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___396_20280.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___396_20280.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___396_20280.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___396_20280.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___396_20280.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___396_20280.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___396_20280.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___396_20280.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20362 =
                    let uu____20363 = guard_of_prob env wl problem t1 t2  in
                    match uu____20363 with
                    | (guard,wl1) ->
                        let uu____20370 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20370
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20581 = br1  in
                        (match uu____20581 with
                         | (p1,w1,uu____20606) ->
                             let uu____20623 = br2  in
                             (match uu____20623 with
                              | (p2,w2,uu____20642) ->
                                  let uu____20647 =
                                    let uu____20648 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20648  in
                                  if uu____20647
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20664 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20664 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20697 = br2  in
                                         (match uu____20697 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20734 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____20734
                                                 in
                                              let uu____20747 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____20770,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____20787) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____20830 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____20830 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____20747
                                                (fun uu____20872  ->
                                                   match uu____20872 with
                                                   | (wprobs,wl2) ->
                                                       let uu____20893 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____20893
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____20908 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____20908
                                                              (fun
                                                                 uu____20932 
                                                                 ->
                                                                 match uu____20932
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21017 -> FStar_Pervasives_Native.None  in
                  let uu____21054 = solve_branches wl brs1 brs2  in
                  (match uu____21054 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21082 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21082 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____21101 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21101  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21110 =
                              let uu____21111 =
                                attempt sub_probs1
                                  (let uu___397_21113 = wl3  in
                                   {
                                     attempting = (uu___397_21113.attempting);
                                     wl_deferred =
                                       (uu___397_21113.wl_deferred);
                                     ctr = (uu___397_21113.ctr);
                                     defer_ok = (uu___397_21113.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___397_21113.tcenv);
                                     wl_implicits =
                                       (uu___397_21113.wl_implicits)
                                   })
                                 in
                              solve env uu____21111  in
                            (match uu____21110 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21117 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21123,uu____21124) ->
                  let head1 =
                    let uu____21148 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21148
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21194 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21194
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21240 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21240
                    then
                      let uu____21241 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21242 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21243 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21241 uu____21242 uu____21243
                    else ());
                   (let no_free_uvars t =
                      (let uu____21253 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21253) &&
                        (let uu____21257 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21257)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21273 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21273 = FStar_Syntax_Util.Equal  in
                    let uu____21274 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21274
                    then
                      let uu____21275 =
                        let uu____21282 = equal t1 t2  in
                        if uu____21282
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21292 = mk_eq2 wl orig t1 t2  in
                           match uu____21292 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21275 with
                      | (guard,wl1) ->
                          let uu____21313 = solve_prob orig guard [] wl1  in
                          solve env uu____21313
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21315,uu____21316) ->
                  let head1 =
                    let uu____21324 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21324
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21370 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21370
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21416 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21416
                    then
                      let uu____21417 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21418 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21419 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21417 uu____21418 uu____21419
                    else ());
                   (let no_free_uvars t =
                      (let uu____21429 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21429) &&
                        (let uu____21433 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21433)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21449 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21449 = FStar_Syntax_Util.Equal  in
                    let uu____21450 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21450
                    then
                      let uu____21451 =
                        let uu____21458 = equal t1 t2  in
                        if uu____21458
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21468 = mk_eq2 wl orig t1 t2  in
                           match uu____21468 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21451 with
                      | (guard,wl1) ->
                          let uu____21489 = solve_prob orig guard [] wl1  in
                          solve env uu____21489
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____21491,uu____21492) ->
                  let head1 =
                    let uu____21494 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21494
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21540 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21540
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21586 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21586
                    then
                      let uu____21587 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21588 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21589 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21587 uu____21588 uu____21589
                    else ());
                   (let no_free_uvars t =
                      (let uu____21599 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21599) &&
                        (let uu____21603 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21603)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21619 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21619 = FStar_Syntax_Util.Equal  in
                    let uu____21620 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21620
                    then
                      let uu____21621 =
                        let uu____21628 = equal t1 t2  in
                        if uu____21628
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21638 = mk_eq2 wl orig t1 t2  in
                           match uu____21638 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21621 with
                      | (guard,wl1) ->
                          let uu____21659 = solve_prob orig guard [] wl1  in
                          solve env uu____21659
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____21661,uu____21662) ->
                  let head1 =
                    let uu____21664 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21664
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21710 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21710
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21756 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21756
                    then
                      let uu____21757 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21758 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21759 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21757 uu____21758 uu____21759
                    else ());
                   (let no_free_uvars t =
                      (let uu____21769 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21769) &&
                        (let uu____21773 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21773)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21789 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21789 = FStar_Syntax_Util.Equal  in
                    let uu____21790 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21790
                    then
                      let uu____21791 =
                        let uu____21798 = equal t1 t2  in
                        if uu____21798
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21808 = mk_eq2 wl orig t1 t2  in
                           match uu____21808 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21791 with
                      | (guard,wl1) ->
                          let uu____21829 = solve_prob orig guard [] wl1  in
                          solve env uu____21829
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____21831,uu____21832) ->
                  let head1 =
                    let uu____21834 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21834
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21880 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21880
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21926 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21926
                    then
                      let uu____21927 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21928 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21929 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21927 uu____21928 uu____21929
                    else ());
                   (let no_free_uvars t =
                      (let uu____21939 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21939) &&
                        (let uu____21943 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21943)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21959 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21959 = FStar_Syntax_Util.Equal  in
                    let uu____21960 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21960
                    then
                      let uu____21961 =
                        let uu____21968 = equal t1 t2  in
                        if uu____21968
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21978 = mk_eq2 wl orig t1 t2  in
                           match uu____21978 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21961 with
                      | (guard,wl1) ->
                          let uu____21999 = solve_prob orig guard [] wl1  in
                          solve env uu____21999
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22001,uu____22002) ->
                  let head1 =
                    let uu____22020 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22020
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22066 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22066
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22112 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22112
                    then
                      let uu____22113 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22114 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22115 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22113 uu____22114 uu____22115
                    else ());
                   (let no_free_uvars t =
                      (let uu____22125 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22125) &&
                        (let uu____22129 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22129)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22145 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22145 = FStar_Syntax_Util.Equal  in
                    let uu____22146 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22146
                    then
                      let uu____22147 =
                        let uu____22154 = equal t1 t2  in
                        if uu____22154
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22164 = mk_eq2 wl orig t1 t2  in
                           match uu____22164 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22147 with
                      | (guard,wl1) ->
                          let uu____22185 = solve_prob orig guard [] wl1  in
                          solve env uu____22185
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22187,FStar_Syntax_Syntax.Tm_match uu____22188) ->
                  let head1 =
                    let uu____22212 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22212
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22258 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22258
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22304 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22304
                    then
                      let uu____22305 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22306 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22307 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22305 uu____22306 uu____22307
                    else ());
                   (let no_free_uvars t =
                      (let uu____22317 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22317) &&
                        (let uu____22321 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22321)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22337 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22337 = FStar_Syntax_Util.Equal  in
                    let uu____22338 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22338
                    then
                      let uu____22339 =
                        let uu____22346 = equal t1 t2  in
                        if uu____22346
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22356 = mk_eq2 wl orig t1 t2  in
                           match uu____22356 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22339 with
                      | (guard,wl1) ->
                          let uu____22377 = solve_prob orig guard [] wl1  in
                          solve env uu____22377
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22379,FStar_Syntax_Syntax.Tm_uinst uu____22380) ->
                  let head1 =
                    let uu____22388 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22388
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22428 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22428
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22468 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22468
                    then
                      let uu____22469 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22470 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22471 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22469 uu____22470 uu____22471
                    else ());
                   (let no_free_uvars t =
                      (let uu____22481 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22481) &&
                        (let uu____22485 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22485)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22501 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22501 = FStar_Syntax_Util.Equal  in
                    let uu____22502 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22502
                    then
                      let uu____22503 =
                        let uu____22510 = equal t1 t2  in
                        if uu____22510
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22520 = mk_eq2 wl orig t1 t2  in
                           match uu____22520 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22503 with
                      | (guard,wl1) ->
                          let uu____22541 = solve_prob orig guard [] wl1  in
                          solve env uu____22541
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22543,FStar_Syntax_Syntax.Tm_name uu____22544) ->
                  let head1 =
                    let uu____22546 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22546
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22586 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22586
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22626 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22626
                    then
                      let uu____22627 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22628 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22629 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22627 uu____22628 uu____22629
                    else ());
                   (let no_free_uvars t =
                      (let uu____22639 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22639) &&
                        (let uu____22643 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22643)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22659 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22659 = FStar_Syntax_Util.Equal  in
                    let uu____22660 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22660
                    then
                      let uu____22661 =
                        let uu____22668 = equal t1 t2  in
                        if uu____22668
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22678 = mk_eq2 wl orig t1 t2  in
                           match uu____22678 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22661 with
                      | (guard,wl1) ->
                          let uu____22699 = solve_prob orig guard [] wl1  in
                          solve env uu____22699
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22701,FStar_Syntax_Syntax.Tm_constant uu____22702) ->
                  let head1 =
                    let uu____22704 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22704
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22744 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22744
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22784 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22784
                    then
                      let uu____22785 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22786 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22787 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22785 uu____22786 uu____22787
                    else ());
                   (let no_free_uvars t =
                      (let uu____22797 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22797) &&
                        (let uu____22801 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22801)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22817 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22817 = FStar_Syntax_Util.Equal  in
                    let uu____22818 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22818
                    then
                      let uu____22819 =
                        let uu____22826 = equal t1 t2  in
                        if uu____22826
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22836 = mk_eq2 wl orig t1 t2  in
                           match uu____22836 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22819 with
                      | (guard,wl1) ->
                          let uu____22857 = solve_prob orig guard [] wl1  in
                          solve env uu____22857
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22859,FStar_Syntax_Syntax.Tm_fvar uu____22860) ->
                  let head1 =
                    let uu____22862 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22862
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22908 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22908
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22954 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22954
                    then
                      let uu____22955 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22956 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22957 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22955 uu____22956 uu____22957
                    else ());
                   (let no_free_uvars t =
                      (let uu____22967 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22967) &&
                        (let uu____22971 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22971)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22987 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22987 = FStar_Syntax_Util.Equal  in
                    let uu____22988 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22988
                    then
                      let uu____22989 =
                        let uu____22996 = equal t1 t2  in
                        if uu____22996
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23006 = mk_eq2 wl orig t1 t2  in
                           match uu____23006 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22989 with
                      | (guard,wl1) ->
                          let uu____23027 = solve_prob orig guard [] wl1  in
                          solve env uu____23027
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23029,FStar_Syntax_Syntax.Tm_app uu____23030) ->
                  let head1 =
                    let uu____23048 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23048
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23088 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23088
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23128 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23128
                    then
                      let uu____23129 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23130 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23131 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23129 uu____23130 uu____23131
                    else ());
                   (let no_free_uvars t =
                      (let uu____23141 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23141) &&
                        (let uu____23145 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23145)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23161 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23161 = FStar_Syntax_Util.Equal  in
                    let uu____23162 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23162
                    then
                      let uu____23163 =
                        let uu____23170 = equal t1 t2  in
                        if uu____23170
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23180 = mk_eq2 wl orig t1 t2  in
                           match uu____23180 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23163 with
                      | (guard,wl1) ->
                          let uu____23201 = solve_prob orig guard [] wl1  in
                          solve env uu____23201
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23203,FStar_Syntax_Syntax.Tm_let uu____23204) ->
                  let uu____23229 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23229
                  then
                    let uu____23230 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23230
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23232,uu____23233) ->
                  let uu____23246 =
                    let uu____23251 =
                      let uu____23252 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23253 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23254 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23255 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23252 uu____23253 uu____23254 uu____23255
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23251)
                     in
                  FStar_Errors.raise_error uu____23246
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23256,FStar_Syntax_Syntax.Tm_let uu____23257) ->
                  let uu____23270 =
                    let uu____23275 =
                      let uu____23276 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23277 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23278 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23279 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23276 uu____23277 uu____23278 uu____23279
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23275)
                     in
                  FStar_Errors.raise_error uu____23270
                    t1.FStar_Syntax_Syntax.pos
              | uu____23280 -> giveup env "head tag mismatch" orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____23341 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23341
           then
             let uu____23342 =
               let uu____23343 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23343  in
             let uu____23344 =
               let uu____23345 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23345  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23342 uu____23344
           else ());
          (let uu____23347 =
             let uu____23348 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23348  in
           if uu____23347
           then
             let uu____23349 =
               let uu____23350 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23351 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23350 uu____23351
                in
             giveup env uu____23349 orig
           else
             (let uu____23353 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23353 with
              | (ret_sub_prob,wl1) ->
                  let uu____23360 =
                    FStar_List.fold_right2
                      (fun uu____23397  ->
                         fun uu____23398  ->
                           fun uu____23399  ->
                             match (uu____23397, uu____23398, uu____23399)
                             with
                             | ((a1,uu____23443),(a2,uu____23445),(arg_sub_probs,wl2))
                                 ->
                                 let uu____23478 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____23478 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23360 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____23507 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____23507  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____23515 = attempt sub_probs wl3  in
                       solve env uu____23515)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23538 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23541)::[] -> wp1
              | uu____23566 ->
                  let uu____23577 =
                    let uu____23578 =
                      let uu____23579 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23579  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23578
                     in
                  failwith uu____23577
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23585 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23585]
              | x -> x  in
            let uu____23587 =
              let uu____23598 =
                let uu____23607 =
                  let uu____23608 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23608 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23607  in
              [uu____23598]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23587;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23625 = lift_c1 ()  in solve_eq uu____23625 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___344_23631  ->
                       match uu___344_23631 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23632 -> false))
                in
             let uu____23633 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23663)::uu____23664,(wp2,uu____23666)::uu____23667)
                   -> (wp1, wp2)
               | uu____23740 ->
                   let uu____23765 =
                     let uu____23770 =
                       let uu____23771 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23772 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23771 uu____23772
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23770)
                      in
                   FStar_Errors.raise_error uu____23765
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23633 with
             | (wpc1,wpc2) ->
                 let uu____23779 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23779
                 then
                   let uu____23782 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23782 wl
                 else
                   (let uu____23784 =
                      let uu____23791 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23791  in
                    match uu____23784 with
                    | (c2_decl,qualifiers) ->
                        let uu____23812 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23812
                        then
                          let c1_repr =
                            let uu____23816 =
                              let uu____23817 =
                                let uu____23818 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____23818  in
                              let uu____23819 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23817 uu____23819
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____23816
                             in
                          let c2_repr =
                            let uu____23821 =
                              let uu____23822 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____23823 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23822 uu____23823
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____23821
                             in
                          let uu____23824 =
                            let uu____23829 =
                              let uu____23830 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____23831 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____23830 uu____23831
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____23829
                             in
                          (match uu____23824 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____23835 = attempt [prob] wl2  in
                               solve env uu____23835)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23846 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23846
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____23849 =
                                     let uu____23856 =
                                       let uu____23857 =
                                         let uu____23874 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____23877 =
                                           let uu____23888 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____23897 =
                                             let uu____23908 =
                                               let uu____23917 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23917
                                                in
                                             [uu____23908]  in
                                           uu____23888 :: uu____23897  in
                                         (uu____23874, uu____23877)  in
                                       FStar_Syntax_Syntax.Tm_app uu____23857
                                        in
                                     FStar_Syntax_Syntax.mk uu____23856  in
                                   uu____23849 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____23968 =
                                    let uu____23975 =
                                      let uu____23976 =
                                        let uu____23993 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____23996 =
                                          let uu____24007 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24016 =
                                            let uu____24027 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24036 =
                                              let uu____24047 =
                                                let uu____24056 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24056
                                                 in
                                              [uu____24047]  in
                                            uu____24027 :: uu____24036  in
                                          uu____24007 :: uu____24016  in
                                        (uu____23993, uu____23996)  in
                                      FStar_Syntax_Syntax.Tm_app uu____23976
                                       in
                                    FStar_Syntax_Syntax.mk uu____23975  in
                                  uu____23968 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24113 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24113
                            then
                              let uu____24114 =
                                let uu____24115 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24115
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24114
                            else ());
                           (let uu____24117 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24117 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24125 =
                                    let uu____24128 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24128
                                     in
                                  solve_prob orig uu____24125 [] wl1  in
                                let uu____24131 = attempt [base_prob] wl2  in
                                solve env uu____24131))))
           in
        let uu____24132 = FStar_Util.physical_equality c1 c2  in
        if uu____24132
        then
          let uu____24133 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24133
        else
          ((let uu____24136 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24136
            then
              let uu____24137 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24138 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24137
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24138
            else ());
           (let uu____24140 =
              let uu____24149 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24152 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24149, uu____24152)  in
            match uu____24140 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24170),FStar_Syntax_Syntax.Total
                    (t2,uu____24172)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24189 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24189 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24190,FStar_Syntax_Syntax.Total uu____24191) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24209),FStar_Syntax_Syntax.Total
                    (t2,uu____24211)) ->
                     let uu____24228 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24228 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24230),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24232)) ->
                     let uu____24249 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24249 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24251),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24253)) ->
                     let uu____24270 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24270 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24271,FStar_Syntax_Syntax.Comp uu____24272) ->
                     let uu____24281 =
                       let uu___398_24284 = problem  in
                       let uu____24287 =
                         let uu____24288 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24288
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24284.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24287;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24284.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24284.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24284.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24284.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24284.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24284.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24284.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24284.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24281 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24289,FStar_Syntax_Syntax.Comp uu____24290) ->
                     let uu____24299 =
                       let uu___398_24302 = problem  in
                       let uu____24305 =
                         let uu____24306 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24306
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24302.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24305;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24302.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24302.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24302.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24302.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24302.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24302.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24302.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24302.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24299 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24307,FStar_Syntax_Syntax.GTotal uu____24308) ->
                     let uu____24317 =
                       let uu___399_24320 = problem  in
                       let uu____24323 =
                         let uu____24324 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24324
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24320.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24320.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24320.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24323;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24320.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24320.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24320.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24320.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24320.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24320.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24317 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24325,FStar_Syntax_Syntax.Total uu____24326) ->
                     let uu____24335 =
                       let uu___399_24338 = problem  in
                       let uu____24341 =
                         let uu____24342 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24342
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24338.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24338.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24338.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24341;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24338.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24338.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24338.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24338.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24338.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24338.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24335 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24343,FStar_Syntax_Syntax.Comp uu____24344) ->
                     let uu____24345 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____24345
                     then
                       let uu____24346 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24346 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24350 =
                            let uu____24355 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24355
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24361 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24362 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24361, uu____24362))
                             in
                          match uu____24350 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____24369 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24369
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24371 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24371 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24374 =
                                  let uu____24375 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24376 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24375 uu____24376
                                   in
                                giveup env uu____24374 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24383 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24383 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24424 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24424 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24442 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24470  ->
                match uu____24470 with
                | (u1,u2) ->
                    let uu____24477 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24478 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24477 uu____24478))
         in
      FStar_All.pipe_right uu____24442 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24505,[])) when
          let uu____24530 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____24530 -> "{}"
      | uu____24531 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24554 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____24554
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24557 =
              FStar_List.map
                (fun uu____24567  ->
                   match uu____24567 with
                   | (uu____24572,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24557 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24577 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24577 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_TypeChecker_Common.prob,worklist)
                  FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____24630 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____24630
                  then
                    let uu____24631 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____24632 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24631
                      (rel_to_string rel) uu____24632
                  else "TOP"  in
                let uu____24634 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____24634 with
                | (p,wl1) ->
                    (def_check_prob (Prims.strcat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv,worklist)
              FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____24692 =
                let uu____24695 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____24695
                 in
              FStar_Syntax_Syntax.new_bv uu____24692 t1  in
            let uu____24698 =
              let uu____24703 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____24703
               in
            match uu____24698 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
           FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____24776 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____24776
              then
                let uu____24777 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24777
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____24799 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____24799
            then
              let uu____24800 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____24800
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____24804 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____24804
             then
               let uu____24805 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____24805
             else ());
            (let f2 =
               let uu____24808 =
                 let uu____24809 = FStar_Syntax_Util.unmeta f1  in
                 uu____24809.FStar_Syntax_Syntax.n  in
               match uu____24808 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____24813 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___400_24814 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___400_24814.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___400_24814.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___400_24814.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicit
                                           Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____24868 =
              let uu____24869 =
                let uu____24870 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____24870;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____24869  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____24868
  
let with_guard_no_simp :
  'Auu____24885 .
    'Auu____24885 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____24908 =
              let uu____24909 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____24909;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____24908
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____24939 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____24939
           then
             let uu____24940 = FStar_Syntax_Print.term_to_string t1  in
             let uu____24941 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24940
               uu____24941
           else ());
          (let uu____24943 =
             let uu____24948 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____24948
              in
           match uu____24943 with
           | (prob,wl) ->
               let g =
                 let uu____24956 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____24966  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____24956  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25000 = try_teq true env t1 t2  in
        match uu____25000 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25004 = FStar_TypeChecker_Env.get_range env  in
              let uu____25005 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25004 uu____25005);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25012 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25012
              then
                let uu____25013 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25014 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25015 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25013
                  uu____25014 uu____25015
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____25037 = FStar_TypeChecker_Env.get_range env  in
          let uu____25038 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25037 uu____25038
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____25063 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25063
         then
           let uu____25064 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25065 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25064 uu____25065
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25068 =
           let uu____25075 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25075 "sub_comp"
            in
         match uu____25068 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25086 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25096  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25086)))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____25141  ->
        match uu____25141 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25184 =
                 let uu____25189 =
                   let uu____25190 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25191 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25190 uu____25191
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25189)  in
               let uu____25192 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25184 uu____25192)
               in
            let equiv1 v1 v' =
              let uu____25204 =
                let uu____25209 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25210 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25209, uu____25210)  in
              match uu____25204 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25229 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25259 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25259 with
                      | FStar_Syntax_Syntax.U_unif uu____25266 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25295  ->
                                    match uu____25295 with
                                    | (u,v') ->
                                        let uu____25304 = equiv1 v1 v'  in
                                        if uu____25304
                                        then
                                          let uu____25307 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25307 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25323 -> []))
               in
            let uu____25328 =
              let wl =
                let uu___401_25332 = empty_worklist env  in
                {
                  attempting = (uu___401_25332.attempting);
                  wl_deferred = (uu___401_25332.wl_deferred);
                  ctr = (uu___401_25332.ctr);
                  defer_ok = false;
                  smt_ok = (uu___401_25332.smt_ok);
                  tcenv = (uu___401_25332.tcenv);
                  wl_implicits = (uu___401_25332.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25350  ->
                      match uu____25350 with
                      | (lb,v1) ->
                          let uu____25357 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25357 with
                           | USolved wl1 -> ()
                           | uu____25359 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25369 =
              match uu____25369 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25378) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____25401,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25403,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25414) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25421,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25429 -> false)
               in
            let uu____25434 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25449  ->
                      match uu____25449 with
                      | (u,v1) ->
                          let uu____25456 = check_ineq (u, v1)  in
                          if uu____25456
                          then true
                          else
                            ((let uu____25459 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25459
                              then
                                let uu____25460 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25461 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25460
                                  uu____25461
                              else ());
                             false)))
               in
            if uu____25434
            then ()
            else
              ((let uu____25465 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25465
                then
                  ((let uu____25467 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25467);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25477 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25477))
                else ());
               (let uu____25487 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25487))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____25554 =
          match uu____25554 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___402_25575 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___402_25575.attempting);
            wl_deferred = (uu___402_25575.wl_deferred);
            ctr = (uu___402_25575.ctr);
            defer_ok;
            smt_ok = (uu___402_25575.smt_ok);
            tcenv = (uu___402_25575.tcenv);
            wl_implicits = (uu___402_25575.wl_implicits)
          }  in
        (let uu____25577 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25577
         then
           let uu____25578 = FStar_Util.string_of_bool defer_ok  in
           let uu____25579 = wl_to_string wl  in
           let uu____25580 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____25578 uu____25579 uu____25580
         else ());
        (let g1 =
           let uu____25583 = solve_and_commit env wl fail1  in
           match uu____25583 with
           | FStar_Pervasives_Native.Some
               (uu____25590::uu____25591,uu____25592) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___403_25617 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___403_25617.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___403_25617.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____25618 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___404_25626 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___404_25626.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___404_25626.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___404_25626.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____25674 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25674 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
  
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___405_25785 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___405_25785.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___405_25785.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___405_25785.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____25786 =
            let uu____25787 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____25787  in
          if uu____25786
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____25795 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____25796 =
                       let uu____25797 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____25797
                        in
                     FStar_Errors.diag uu____25795 uu____25796)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____25801 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____25802 =
                        let uu____25803 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____25803
                         in
                      FStar_Errors.diag uu____25801 uu____25802)
                   else ();
                   (let uu____25806 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____25806
                      "discharge_guard'" env vc1);
                   (let uu____25807 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____25807 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____25814 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25815 =
                                let uu____25816 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____25816
                                 in
                              FStar_Errors.diag uu____25814 uu____25815)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____25821 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25822 =
                                let uu____25823 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____25823
                                 in
                              FStar_Errors.diag uu____25821 uu____25822)
                           else ();
                           (let vcs =
                              let uu____25834 = FStar_Options.use_tactics ()
                                 in
                              if uu____25834
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____25854  ->
                                     (let uu____25856 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a236  -> ())
                                        uu____25856);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____25899  ->
                                              match uu____25899 with
                                              | (env1,goal,opts) ->
                                                  let uu____25915 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____25915, opts)))))
                              else
                                (let uu____25917 =
                                   let uu____25924 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____25924)  in
                                 [uu____25917])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____25957  ->
                                    match uu____25957 with
                                    | (env1,goal,opts) ->
                                        let uu____25967 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____25967 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____25975 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25976 =
                                                   let uu____25977 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____25978 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____25977 uu____25978
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25975 uu____25976)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____25981 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25982 =
                                                   let uu____25983 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____25983
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25981 uu____25982)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____25997 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25997 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26004 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26004
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26015 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26015 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26041 = try_teq false env t1 t2  in
        match uu____26041 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let unresolved ctx_u =
            let uu____26076 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26076 with
            | FStar_Pervasives_Native.Some uu____26079 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26099 = acc  in
            match uu____26099 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26111 = hd1  in
                     (match uu____26111 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26116;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26124 = unresolved ctx_u  in
                             if uu____26124
                             then
                               match hd1.FStar_TypeChecker_Env.imp_meta with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env1,tau) ->
                                   let t =
                                     env1.FStar_TypeChecker_Env.synth_hook
                                       env1
                                       (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                       tau
                                      in
                                   let extra =
                                     let uu____26139 = teq_nosmt env1 t tm
                                        in
                                     match uu____26139 with
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "resolve_implicits: unifying with an unresolved uvar failed?"
                                     | FStar_Pervasives_Native.Some g1 ->
                                         g1.FStar_TypeChecker_Env.implicits
                                      in
                                   let hd2 =
                                     let uu___406_26148 = hd1  in
                                     {
                                       FStar_TypeChecker_Env.imp_reason =
                                         (uu___406_26148.FStar_TypeChecker_Env.imp_reason);
                                       FStar_TypeChecker_Env.imp_uvar =
                                         (uu___406_26148.FStar_TypeChecker_Env.imp_uvar);
                                       FStar_TypeChecker_Env.imp_tm =
                                         (uu___406_26148.FStar_TypeChecker_Env.imp_tm);
                                       FStar_TypeChecker_Env.imp_range =
                                         (uu___406_26148.FStar_TypeChecker_Env.imp_range);
                                       FStar_TypeChecker_Env.imp_meta =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   until_fixpoint (out, changed) (hd2 ::
                                     (FStar_List.append extra tl1))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___407_26156 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___407_26156.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___407_26156.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___407_26156.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___407_26156.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___407_26156.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___407_26156.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___407_26156.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___407_26156.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___407_26156.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___407_26156.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___407_26156.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___407_26156.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___407_26156.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___407_26156.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___407_26156.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___407_26156.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___407_26156.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___407_26156.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___407_26156.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___407_26156.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___407_26156.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___407_26156.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___407_26156.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___407_26156.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___407_26156.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___407_26156.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___407_26156.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___407_26156.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___407_26156.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___407_26156.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___407_26156.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___407_26156.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___407_26156.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___407_26156.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___407_26156.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___407_26156.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___407_26156.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___407_26156.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___407_26156.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___407_26156.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___407_26156.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___408_26159 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___408_26159.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___408_26159.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___408_26159.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___408_26159.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___408_26159.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___408_26159.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___408_26159.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___408_26159.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___408_26159.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___408_26159.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___408_26159.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___408_26159.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___408_26159.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___408_26159.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___408_26159.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___408_26159.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___408_26159.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___408_26159.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___408_26159.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___408_26159.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___408_26159.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___408_26159.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___408_26159.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___408_26159.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___408_26159.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___408_26159.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___408_26159.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___408_26159.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___408_26159.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___408_26159.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___408_26159.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___408_26159.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___408_26159.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___408_26159.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___408_26159.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26162 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26162
                                   then
                                     let uu____26163 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26164 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26165 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26166 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26163 uu____26164 uu____26165
                                       reason uu____26166
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___410_26170  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26177 =
                                             let uu____26186 =
                                               let uu____26193 =
                                                 let uu____26194 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26195 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26196 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26194 uu____26195
                                                   uu____26196
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26193, r)
                                                in
                                             [uu____26186]  in
                                           FStar_Errors.add_errors
                                             uu____26177);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___411_26210 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___411_26210.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___411_26210.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___411_26210.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26213 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26223  ->
                                               let uu____26224 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26225 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26226 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26224 uu____26225
                                                 reason uu____26226)) env2 g2
                                         true
                                        in
                                     match uu____26213 with
                                     | FStar_Pervasives_Native.Some g3 -> g3
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Env.implicits
                                         out), true) tl1)))))
             in
          let uu___412_26228 = g  in
          let uu____26229 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___412_26228.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___412_26228.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___412_26228.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26229
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____26263 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26263 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26264 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a237  -> ()) uu____26264
      | imp::uu____26266 ->
          let uu____26269 =
            let uu____26274 =
              let uu____26275 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26276 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26275 uu____26276 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26274)
             in
          FStar_Errors.raise_error uu____26269
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26292 = teq_nosmt env t1 t2  in
        match uu____26292 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___413_26307 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___413_26307.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___413_26307.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___413_26307.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26342 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26342
         then
           let uu____26343 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26344 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26343
             uu____26344
         else ());
        (let uu____26346 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26346 with
         | (prob,x,wl) ->
             let g =
               let uu____26365 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26375  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26365  in
             ((let uu____26395 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26395
               then
                 let uu____26396 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26397 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26398 =
                   let uu____26399 = FStar_Util.must g  in
                   guard_to_string env uu____26399  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26396 uu____26397 uu____26398
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26433 = check_subtyping env t1 t2  in
        match uu____26433 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26452 =
              let uu____26453 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____26453 g  in
            FStar_Pervasives_Native.Some uu____26452
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26471 = check_subtyping env t1 t2  in
        match uu____26471 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26490 =
              let uu____26491 =
                let uu____26492 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26492]  in
              FStar_TypeChecker_Env.close_guard env uu____26491 g  in
            FStar_Pervasives_Native.Some uu____26490
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26529 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26529
         then
           let uu____26530 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26531 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26530
             uu____26531
         else ());
        (let uu____26533 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26533 with
         | (prob,x,wl) ->
             let g =
               let uu____26548 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____26558  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26548  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26581 =
                      let uu____26582 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26582]  in
                    FStar_TypeChecker_Env.close_guard env uu____26581 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26619 = subtype_nosmt env t1 t2  in
        match uu____26619 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  