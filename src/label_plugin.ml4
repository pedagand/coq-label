(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Genintern
open Constrintern
open Pcoq.Constr
open Pp
open Ltac_plugin

DECLARE PLUGIN "label_plugin"

(* Search for the pattern [patt] in the context. *)
let label ?(concl=false) patt =
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
      Constr_matching.is_matching env sigma patt typ
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
let pr_label_patt _ _ _ _ = mt ()
let interp_label_patt ist gl pat = (Tacmach.project gl, pat)
let glob_label_patt ist pat =
  let ltacsign = { ltac_vars = ist.ltacvars
                 ; ltac_bound = Names.Id.Set.empty
                 ; ltac_extra = Genintern.Store.empty }
  in
  snd (intern_constr_pattern ~ltacvars:ltacsign ist.genv (Evd.from_env ist.genv) pat)
let subst_label_patt subst pat = Patternops.subst_pattern subst pat

ARGUMENT EXTEND label_patt
    PRINTED BY pr_label_patt
    INTERPRETED BY interp_label_patt
    GLOBALIZED BY glob_label_patt
    SUBSTITUTED BY subst_label_patt
    RAW_PRINTED BY pr_label_patt
    GLOB_PRINTED BY pr_label_patt
 [ lconstr(c) ] ->  [ c ]
END

(* Manually register [label] as an ML tactic *)

let label_name concl =
  let suff = if concl then "std" else "concl" in
  { Tacexpr.mltac_tactic = Printf.sprintf "label_%s" suff ;
    Tacexpr.mltac_plugin = "label_plugin" }

let label_entry concl =
  { Tacexpr.mltac_index = 0;
    Tacexpr.mltac_name = label_name concl }

let _ =
  let label concl = fun [c] _ ->
    label ~concl:concl (Tacinterp.Value.cast (Genarg.topwit wit_label_patt) c)
  in
  Tacenv.register_ml_tactic (label_name true) [| label true |];
  Tacenv.register_ml_tactic (label_name false) [| label false |]


(* Extend grammar with labels. *)

module Gram = Pcoq.Gram
open Pcoq.Constr
open Constrexpr

let register concl p =
  let argp = Genarg.in_gen (Genarg.rawwit wit_label_patt) p in
  let tac = Tacexpr.TacML (Loc.tag (label_entry concl, [Tacexpr.TacGeneric argp])) in
  let arg = Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) tac in
  CHole (None, IntroAnonymous, Some arg)

GEXTEND Gram
  GLOBAL: operconstr ;

  operconstr:
    [ "200" [ "\\<"; p = label_patt; "\\>" -> CAst.make @@ register false p
            | "\\<<"; p = label_patt; "\\>>" -> CAst.make @@ register true p ]]
    ;
END;;
