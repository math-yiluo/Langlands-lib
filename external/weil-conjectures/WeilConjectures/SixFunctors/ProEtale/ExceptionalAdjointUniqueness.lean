/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!
# The ambient exceptional adjoint restricts to the constructible one

Blueprint `sk-def-sf-admissible` distinguishes the ambient exceptional right adjoint datum (1)
of a separated finite-type `f : X ⟶ Y` from the stronger admissibility datum (1)–(3), and
observes that when (1)–(3) hold, the restriction to `Dctf` of a right adjoint `Rf^×` of
`Rf_!` on the unbounded pro-étale derived categories coincides, by uniqueness of adjoints, with
the constructible exceptional inverse image `Rf^!` of `theorem-f-shriek-ell-adic-coefficients--4`
(vi) (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`).

The uniqueness is that of representing objects: for a bounded below `L` with `Rf^× L` bounded
below of étale origin, `Rf^× L` and `Rf^! L` both represent `K ↦ Hom(Rf_! K, L)` on the objects
`K` bounded below of étale origin (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`),
so they are isomorphic, by an isomorphism compatible with the counits
(`AlgebraicGeometry.ProEtale.rightAdjointObjIsoRightDerivedUpperShriekObj`). Clause (3) of the
admissibility datum puts `Rf^× L` in `Dctf(X, A)` for `L ∈ Dctf(Y, A)`, whence the natural
isomorphism `Rf^×|_{Dctf} ≅ Rf^!|_{Dctf}`
(`IsExceptionalAdjointAdmissible.rightAdjointIsoRightDerivedUpperShriek`).

The blueprint's warning that neither datum holds in general is
`AlgebraicGeometry.ProEtale.not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety`
(`sk-rem-sf-fullcd-scope`), and hence
`AlgebraicGeometry.ProEtale.not_isExceptionalAdjointAdmissible_of_isAbelianVariety` for the
admissibility datum, which contains the ambient one
(`AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible.toHasAmbientExceptionalRightAdjoint`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

section Uniqueness

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
  {G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
  (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⊣ G)

/-- Blueprint `sk-def-sf-admissible`: uniqueness of the exceptional adjoint.

If `G` is a right adjoint of the pro-étale `Rf_!` on the unbounded derived categories, `L` is
bounded below and `G L` is bounded below of étale origin, then `G L ≅ Rf^! L`: both represent
`K ↦ Hom(Rf_! K, L)` on the objects bounded below of étale origin. The isomorphism is the
adjunct, under the constructible exceptional adjunction, of the counit `Rf_! G L ⟶ L` of `G`. -/
noncomputable def rightAdjointObjIsoRightDerivedUpperShriekObj
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hGL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X (G.obj L)) :
    G.obj L ≅ (R(f)^![Λ]).obj L where
  hom := rightDerivedUpperShriekHomEquiv f hGL hL (adj.counit.app L)
  inv := adj.homEquiv _ _ (rightDerivedUpperShriekCounit f L hL)
  hom_inv_id := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
      ← rightDerivedUpperShriekHomEquiv_symm_apply f hGL hL, Equiv.symm_apply_apply,
      Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  inv_hom_id := by
    have hRL := plusEtaleOrigin_rightDerivedUpperShriek_obj f hL
    apply (rightDerivedUpperShriekHomEquiv f hRL hL).symm.injective
    rw [rightDerivedUpperShriekHomEquiv_symm_apply, Functor.map_comp, Category.assoc,
      ← rightDerivedUpperShriekHomEquiv_symm_apply f hGL hL, Equiv.symm_apply_apply,
      ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply,
      rightDerivedUpperShriekHomEquiv_symm_id]

/-- The isomorphism `G L ≅ Rf^! L` is compatible with the counits: the counit of `G` at `L` is
`Rf_!` of it followed by the counit `ε_L` of the constructible exceptional adjunction. -/
lemma rightDerivedLowerShriek_map_rightAdjointObjIsoRightDerivedUpperShriekObj_hom_comp
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hGL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X (G.obj L)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
        (rightAdjointObjIsoRightDerivedUpperShriekObj f adj hL hGL).hom ≫
      rightDerivedUpperShriekCounit f L hL = adj.counit.app L := by
  rw [← rightDerivedUpperShriekHomEquiv_symm_apply f hGL hL]
  exact Equiv.symm_apply_apply _ _

/-- The isomorphisms `G L ≅ Rf^! L` are natural in `L`. -/
lemma rightAdjointObjIsoRightDerivedUpperShriekObj_hom_naturality
    {L L' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hGL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X (G.obj L))
    (hL' : _root_.DerivedCategory.TStructure.t.plus L')
    (hGL' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X (G.obj L')) (φ : L ⟶ L') :
    G.map φ ≫ (rightAdjointObjIsoRightDerivedUpperShriekObj f adj hL' hGL').hom =
      (rightAdjointObjIsoRightDerivedUpperShriekObj f adj hL hGL).hom ≫ (R(f)^![Λ]).map φ := by
  simp only [rightAdjointObjIsoRightDerivedUpperShriekObj]
  rw [← rightDerivedUpperShriekHomEquiv_naturality_left f hGL hGL' hL',
    Adjunction.counit_naturality, rightDerivedUpperShriekHomEquiv_naturality_right f hGL hL hL']

end Uniqueness

section Admissibility

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] [CompactSpace Y]
  {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-def-sf-admissible`: under the admissibility datum (1)–(3), the restriction of
every right adjoint `Rf^×` of `Rf_!` to `Dctf(Y, Λ)`, for a finite coefficient ring `Λ`, is the
constructible exceptional inverse image `Rf^!` of `theorem-f-shriek-ell-adic-coefficients--4` (vi),
by uniqueness of adjoints: clause (3) puts `Rf^× L` in `Dctf(X, Λ)`, which consists of objects
bounded below of étale origin, and there `Rf^×` and `Rf^!` represent the same functor
(`AlgebraicGeometry.ProEtale.rightAdjointObjIsoRightDerivedUpperShriekObj`). -/
noncomputable def IsExceptionalAdjointAdmissible.rightAdjointIsoRightDerivedUpperShriek
    (h : IsExceptionalAdjointAdmissible (ModuleCat.{u + 1} Λ) f)
    {G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⊣ G) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙ G ≅
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙ R(f)^![Λ] :=
  NatIso.ofComponents
    (fun L ↦ rightAdjointObjIsoRightDerivedUpperShriekObj f adj L.property.plus
      (h.constructibleFiniteTor_le_inverseImage adj _ L.property).plusEtaleOrigin)
    (fun φ ↦ rightAdjointObjIsoRightDerivedUpperShriekObj_hom_naturality f adj _ _ _ _
      φ.hom)

omit [CompactSpace Y] in
/-- Blueprint `sk-def-sf-admissible`: the admissibility datum contains the ambient datum (1). -/
theorem IsExceptionalAdjointAdmissible.hasAmbientExceptionalRightAdjoint
    (h : IsExceptionalAdjointAdmissible A f) : HasAmbientExceptionalRightAdjoint A f :=
  h.toHasAmbientExceptionalRightAdjoint

end Admissibility

section AbelianVariety

variable (Λ : Type (u + 1)) [Field Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]

set_option linter.unusedSectionVars false in
/-- Blueprint `sk-def-sf-admissible` (warning): neither the ambient datum nor the admissibility
datum may be presupposed for the structure morphism of a smooth proper variety: for an elliptic
curve (more generally an abelian variety of positive dimension) over an algebraically closed
field, the structure morphism carries no admissibility datum, since it does not even carry the
ambient datum (`not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety`,
`sk-rem-sf-fullcd-scope`). -/
theorem not_isExceptionalAdjointAdmissible_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ IsExceptionalAdjointAdmissible (ModuleCat.{u + 1} Λ) E.hom := fun h ↦
  not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety Λ E hE
    h.hasAmbientExceptionalRightAdjoint

end AbelianVariety

end ProEtale

end AlgebraicGeometry
