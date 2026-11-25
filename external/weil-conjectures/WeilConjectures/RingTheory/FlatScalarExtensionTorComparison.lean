/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule

/-! # Tor comparison for flat extension of scalars
Source: Weibel, An Introduction to Homological Algebra, Corollary 4.3.6,
pp. 101–102, projective-resolution argument.
(blueprint: lem-pc-flat-scalar-extension-tor-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat

/-- Flat scalar extension commutes with Tor after restricting the result.
Source: Weibel, An Introduction to Homological Algebra, Corollary 4.3.6,
p. 101, its projective-resolution argument; tensor associativity.
Proof: extend a projective resolution of L along the flat ring map f. Extension
is exact and preserves projectives by its adjunction with exact restriction,
so it gives a projective resolution of the induced module. In every degree,
identify (S tensor_R P) tensor_S N with P tensor_R N, restricted to R,
using tensor commutativity and cancellation of scalar extension. Naturality
makes these maps a chain isomorphism. Restriction is exact and therefore
commutes with homology. The projective-resolution computation of Tor gives
the claimed isomorphism. Flatness is the only hypothesis; degree zero, zero
rings, and zero modules are included.
(blueprint: lem-pc-flat-scalar-extension-tor-comparison) -/
theorem nonempty_flat_scalar_extension_tor_iso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (L : ModuleCat.{u} R) (N : ModuleCat.{u} S) (i : ℕ) :
    Nonempty ((restrictScalars f).obj
      (((Tor' (ModuleCat.{u} S) i).obj ((extendScalars f).obj L)).obj N) ≅
      (((Tor' (ModuleCat.{u} R) i).obj L).obj ((restrictScalars f).obj N))) := by
  classical
  let E := extendScalars.{u, u, u} f
  let U := restrictScalars.{u, u, u} f
  have : PreservesFiniteLimits E := preservesFiniteLimits_extendScalars_of_flat hf
  have : E.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj f)
  have : E.Additive := (extendRestrictScalarsAdj f).left_adjoint_additive
  let P := projectiveResolution L
  let Q := E.mapProjectiveResolution P
  let F := (tensoringRight (ModuleCat.{u} S)).obj N
  let G := (tensoringRight (ModuleCat.{u} R)).obj (U.obj N)
  obtain ⟨e, he⟩ := exists_tensorRestrictExtend_module_natural f
  let c (X : ModuleCat.{u} R) : U.obj (E.obj X ⊗ N) ≅ X ⊗ U.obj N :=
    U.mapIso (β_ (E.obj X) N) ≪≫ e N X ≪≫ β_ (U.obj N) X
  let K := (F.mapHomologicalComplex (.down ℕ)).obj Q.complex
  let K' := (G.mapHomologicalComplex (.down ℕ)).obj P.complex
  let t : (U.mapHomologicalComplex (.down ℕ)).obj K ≅ K' :=
    HomologicalComplex.Hom.isoOfComponents (fun j ↦ c (P.complex.X j)) (by
      intro j k hjk
      change (c (P.complex.X j)).hom ≫ G.map (P.complex.d j k) =
        U.map (F.map (E.map (P.complex.d j k))) ≫ (c (P.complex.X k)).hom
      dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Category.assoc]
      change U.map (β_ (E.obj (P.complex.X j)) N).hom ≫
        (e N (P.complex.X j)).hom ≫ (β_ (U.obj N) (P.complex.X j)).hom ≫
          P.complex.d j k ▷ U.obj N =
        U.map (E.map (P.complex.d j k) ▷ N) ≫
          U.map (β_ (E.obj (P.complex.X k)) N).hom ≫
            (e N (P.complex.X k)).hom ≫ (β_ (U.obj N) (P.complex.X k)).hom
      rw [← BraidedCategory.braiding_naturality_right]
      have hn := he N N (P.complex.X j) (P.complex.X k) (𝟙 N) (P.complex.d j k)
      change U.map (N ◁ E.map (P.complex.d j k)) ≫ (e N (P.complex.X k)).hom =
        (e N (P.complex.X j)).hom ≫ U.obj N ◁ P.complex.d j k at hn
      rw [← Category.assoc (e N (P.complex.X j)).hom,
        ← hn, Category.assoc]
      rw [← Functor.map_comp_assoc, ← BraidedCategory.braiding_naturality_left,
        Functor.map_comp_assoc])
  exact ⟨U.mapIso (Q.isoLeftDerivedObj F i) ≪≫
    ((K.sc i).mapHomologyIso U).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso t ≪≫
    (P.isoLeftDerivedObj G i).symm⟩

end ModuleCat
