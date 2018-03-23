(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Genintern
open Constrintern
open Pcoq.Constr
open Pp
open Ltac_plugin

DECLARE PLUGIN "cortouche_plugin"

(* Search for the pattern [patt] in the context. *)
let cartouche ?(concl=false) patt =
  Proofview.Goal.nf_enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    let is_matching_patt hyp =
      let typ = Context.Named.Declaration.get_type hyp in
      let typ = if not concl then typ 
                else snd (EConstr.decompose_prod_assum sigma typ) in
      Printf.ifprintf stderr "Checking pattern %s against conclusion %s\n"
                      (Pp.string_of_ppcmds (Printer.pr_constr_pattern_env env sigma patt))
                      (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma typ));
      Constr_matching.is_matching_conv env sigma patt typ
    in
    let wit = List.find_all is_matching_patt hyps in
    match wit with
    | [] -> 
       Tacticals.New.tclZEROMSG (str "No such assumption.")
    | [ wit ] ->
       let (_,sort) = Typing.type_of env sigma (Context.Named.Declaration.get_type wit) in
       let wit = Constr.mkVar (Context.Named.Declaration.get_id wit) in
       let insert_wit h = (h, EConstr.of_constr wit) in
       if Termops.is_Prop sigma sort then
         Refine.refine ~typecheck:true insert_wit
       else
         Tacticals.New.tclZEROMSG (str "Found a proof-relevant assumption.")
    | _ -> 
       Tacticals.New.tclZEROMSG (str "This pattern is ambiguous.")
  end

(* Extend tactic argument's syntax with pattern  *)
let pr_cartouche_patt _ _ _ _ = mt ()
let interp_cartouche_patt ist gl pat = (Tacmach.project gl, pat)
let glob_cartouche_patt ist pat =  
  let ltacsign = { ltac_vars = ist.ltacvars
                 ; ltac_bound = Names.Id.Set.empty
                 ; ltac_extra = Genintern.Store.empty }
  in
  snd (intern_constr_pattern ~ltacvars:ltacsign ist.genv pat)
let subst_cartouche_patt subst pat = Patternops.subst_pattern subst pat

ARGUMENT EXTEND cartouche_patt 
    PRINTED BY pr_cartouche_patt 
    INTERPRETED BY interp_cartouche_patt
    GLOBALIZED BY glob_cartouche_patt
    SUBSTITUTED BY subst_cartouche_patt
    RAW_PRINTED BY pr_cartouche_patt
    GLOB_PRINTED BY pr_cartouche_patt
 [ lconstr(c) ] ->  [ c ]
END

(* Manually register [cartouche] as an ML tactic *)

let cortouche_name concl = 
  let suff = if concl then "std" else "concl" in
  { Tacexpr.mltac_tactic = Printf.sprintf "cartouche_%s" suff ;
    Tacexpr.mltac_plugin = "cortouche_plugin" }

let cortouche_entry concl =
  { Tacexpr.mltac_index = 0;
    Tacexpr.mltac_name = cortouche_name concl }

let _ =
  let cartouche concl = fun [c] _ -> 
    cartouche ~concl:concl (Tacinterp.Value.cast (Genarg.topwit wit_cartouche_patt) c)
  in
  Tacenv.register_ml_tactic (cortouche_name true) [| cartouche true |];
  Tacenv.register_ml_tactic (cortouche_name false) [| cartouche false |]


(* Extend grammar with cartouches. *)

module Gram = Pcoq.Gram
open Pcoq.Constr
open Constrexpr

let register concl p =
  let argp = Genarg.in_gen (Genarg.rawwit wit_cartouche_patt) p in
  let tac = Tacexpr.TacML (Loc.tag (cortouche_entry concl, [Tacexpr.TacGeneric argp])) in
  let arg = Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) tac in
  CHole (None, IntroAnonymous, Some arg)

GEXTEND Gram
  GLOBAL: operconstr ;

  operconstr:
    [ "200" [ "\\<"; p = cartouche_patt; "\\>" -> CAst.make @@ register false p
            | "\\<<"; p = cartouche_patt; "\\>>" -> CAst.make @@ register true p ]]
    ;
END;;
