# Cortouche: the end of H, H0, H1, ...


## Synopsis

Cortouche is a Coq plugin for referring to propositional assumptions
without systematically resorting to tedious (or, worse, automatic)
naming of hypothesis. To this end, we allow the user to write a
pattern to refer to the (unique) assumption matching this pattern in
the context.

An alternative to this plugin is Pierre Courtieu's
[LibHypsNaming](http://cedric.cnam.fr/~courtiep/downloads/LibHypsNaming.v)
Ltac library, which computes the name of assumptions from their types.

## Code Example

Let us consider a (propositional) predicate `is_foo` over some types
`typ` and `exp`.

    Parameter typ: Type.
    Parameter exp: Type.
    Parameter is_foo: exp -> typ -> Prop.

Wherever Coq expects an identifier referring to an assumption, we can
provide a cortouche that will search for a type matching a given
pattern. In the following example, we can return the desired argument
by referring to its type:

    Lemma example: 
      forall t e1 e2 , 
        is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
    Proof.
      intros.
      exact (\< is_foo e1 t \>).
    Qed.

In fact, our pattern could have been more general since there is no
other assumption matching `is_foo e1`:

    Lemma example_patt: 
      forall t e1 e2 , 
        is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
    Proof.
      intros.
      exact (\< is_foo e1 _ \>).
    Qed.

Nonetheless, if we are too general and do not mention `e1`, the
cortouche is ambiguous and will be rejected:

    Lemma example_too_general: 
      forall t e1 e2 , 
        is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
    Proof.
      intros.
      Fail exact (\< is_foo _ _ \>).
    Abort.

Finally, if we want to match the end of a type telescope, we must
explicitly request it through a double cortouche:

    Lemma example_concl: 
      (forall e t, is_foo e t) -> forall e t, is_foo e t.
    Proof.
      intros.
      exact (\<< is_foo _ _ \>>).
    Qed.

## Installation

Assuming that you have a working installation of Coq.trunk, do `make`.
This will consecutively build the plugin and the supporting theories.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.coqrc`:

    Add Rec LoadPath "path_to_cortouche/theories" as Cortouche.
    Add ML Path "path_to_cortouche/src".

## Contributors

+ [Pierre-Évariste Dagand](https://pages.lip6.fr/Pierre-Evariste.Dagand/)
+ [Théo Zimmermann](http://www.theozimmermann.net/fr/)

## License

Distributed under the terms of the MIT license.
