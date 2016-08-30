(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Genintern
open Constrintern
open Pcoq.Constr
open Pp
open Proofview.Notations

DECLARE PLUGIN "cortouche_plugin"

(* Search for the pattern [patt] in the context. *)
let cartouche patt =
  Proofview.Goal.nf_enter { Proofview.Goal.enter = begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    try
      let is_matching_patt hyp =         
        let typ = Context.Named.Declaration.get_type hyp in
        Constr_matching.is_matching_conv env sigma patt typ
      in
      let wit = List.find is_matching_patt hyps in
      let (_,sort) = Typing.type_of env sigma (Context.Named.Declaration.get_type wit) in
      if Term.is_Prop sort then
        Refine.refine ~unsafe:false { Sigma.run = fun h -> 
          Sigma.here (Constr.mkVar (Context.Named.Declaration.get_id wit)) h }
      else
        Tacticals.New.tclZEROMSG (str "Found a proof-relevant assumption: abort.")
    with
    | _ ->
       Tacticals.New.tclZEROMSG (str "No such assumption.")
  end }

(* Extend tactic argument's syntax with pattern  *)
let pr_cartouche_patt _ _ _ _ = mt ()
let interp_cartouche_patt ist gl pat = (Tacmach.project gl, pat)
let glob_cartouche_patt ist pat =  
  let ltacsign = { ltac_vars = ist.ltacvars
                 ; ltac_bound = Names.Id.Set.empty }
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

module Gram = Pcoq.Gram
open Pcoq.Constr
open Constrexpr
open Compat

(*
  XXX: We don't actually use this syntax, we just take advantage of
       [TACTIC EXTEND] to inject the ML tactic in the system. 
  TODO: Look into [Ltac.Tacenv] to manually register [cartouche]
*)
TACTIC EXTEND cartouche
[ "of" cartouche_patt(c) ] ->  [ cartouche c ]
END;;

(* Extend grammar with cartouches. *)

GEXTEND Gram
  GLOBAL: operconstr ;

  operconstr:
    [ "200" [ "\\<"; p = cartouche_patt; "\\>" -> 
      let cartouche_entry = 
        { Tacexpr.mltac_index = 0 ;
          Tacexpr.mltac_name = 
            { Tacexpr.mltac_tactic = "cartouche";
              Tacexpr.mltac_plugin = "cortouche_plugin" } }
      in
      let argp = Genarg.in_gen (Genarg.rawwit wit_cartouche_patt) p in
      let tac = Tacexpr.TacML (!@loc, cartouche_entry, [Tacexpr.TacGeneric argp]) in
      let arg = Genarg.in_gen (Genarg.rawwit Constrarg.wit_tactic) tac in
      CHole (!@loc, None, IntroAnonymous, Some arg) ]]
    ;
END;;
