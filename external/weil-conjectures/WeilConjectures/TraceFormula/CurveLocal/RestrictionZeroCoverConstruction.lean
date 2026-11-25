/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationFiniteBaseChange
public import WeilConjectures.TraceFormula.CurveLocal.BlowupRestriction
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverDatum

/-!

# The surface `T'` of a cover datum

For a cover datum `p : C ⟶ X`, `c` of blueprint `lemma-tangent-cones-on-cover`, let
`S' = C ×_k C`, `s' = (c, c)` and `T'` the strict localization of `S'` at `s'`
(`AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.T'`), with the morphism `π : T' ⟶ T` induced
by `p × p` (`AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.π`). The curves `D' = G' ∪ V'`,
`H'`, `B'` of `T'` are the reduced inverse images of `G ∪ V`, `H`, `B`
(`AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.dD'` etc.).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {M : CurveLocalModel k} {ℓ : ℕ}
  {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

attribute [instance] CoverDatum.smoothOfRelativeDimension CoverDatum.isSeparated
  CoverDatum.isFinite

/-- The surface `S' = C ×_k C`. -/
noncomputable abbrev S' : Scheme.{u} := pullback D.fC D.fC

omit [IsAlgClosed k] in
lemma c_comp_fC : D.c ≫ D.fC = 𝟙 _ := by
  rw [← D.p_comp, ← Category.assoc, D.c_comp, M.y_comp]

/-- The `k`-point `(c, c)` of `S'`. -/
noncomputable def s' : Spec (.of k) ⟶ D.S' := pullback.lift D.c D.c rfl

/-- The strict localization `T'` of `S'` at `(c, c)`. -/
noncomputable abbrev T' : Scheme.{u} := strictLocalization D.s'

/-- The morphism `p × p : S' ⟶ X ×_k X`. -/
noncomputable def g : D.S' ⟶ pullback M.f M.f :=
  pullback.map _ _ _ _ D.p D.p (𝟙 _) (by rw [D.p_comp, Category.comp_id])
    (by rw [D.p_comp, Category.comp_id])

omit [IsAlgClosed k] in
lemma s'_comp_g : D.s' ≫ D.g = M.diagPoint := by
  apply pullback.hom_ext <;> simp [s', g, diagPoint, D.c_comp]

/-- The morphism `π : T' ⟶ T` induced by `p × p`. -/
noncomputable def π : D.T' ⟶ M.T :=
  strictLocalizationMap D.g D.s' ≫ eqToHom (by rw [s'_comp_g])


omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma g_fst : D.g ≫ pullback.fst M.f M.f = pullback.fst D.fC D.fC ≫ D.p :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma g_snd : D.g ≫ pullback.snd M.f M.f = pullback.snd D.fC D.fC ≫ D.p :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma s'_fst : D.s' ≫ pullback.fst D.fC D.fC = D.c :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma s'_snd : D.s' ≫ pullback.snd D.fC D.fC = D.c :=
  pullback.lift_snd _ _ _

/-- Transport of strict localizations along an equality of points. -/
lemma eqToHom_comp_strictLocalizationToBase {S : Scheme.{u}} {a b : Spec (.of k) ⟶ S}
    (e : a = b) (h : strictLocalization a = strictLocalization b) :
    eqToHom h ≫ strictLocalizationToBase b = strictLocalizationToBase a := by
  subst e
  simp

/-- `π` is compatible with `p × p`. -/
lemma π_comp_τ : D.π ≫ M.τ = strictLocalizationToBase D.s' ≫ D.g := by
  rw [π, Category.assoc, eqToHom_comp_strictLocalizationToBase D.s'_comp_g,
    strictLocalizationMap_comp_strictLocalizationToBase]
/-- The reduced inverse image `D' = G' ∪ V'` of the graph and the vertical axis. -/
noncomputable abbrev D' : Scheme.{u} :=
  reducedClosed (strictHenselization D.s') (D.π.base ⁻¹' (Set.range M.a.base ∪ Set.range M.v.base))

/-- The closed immersion `D' ⟶ T'`. -/
noncomputable abbrev dD' : D.D' ⟶ D.T' := reducedClosedι _ _

/-- The reduced inverse image `H'` of the horizontal axis. -/
noncomputable abbrev H' : Scheme.{u} :=
  reducedClosed (strictHenselization D.s') (D.π.base ⁻¹' Set.range M.hH.base)

/-- The closed immersion `H' ⟶ T'`. -/
noncomputable abbrev dH' : D.H' ⟶ D.T' := reducedClosedι _ _

/-- The reduced inverse image `B'` of the diagonal. -/
noncomputable abbrev B' : Scheme.{u} :=
  reducedClosed (strictHenselization D.s') (D.π.base ⁻¹' Set.range M.b.base)

/-- The closed immersion `B' ⟶ T'`. -/
noncomputable abbrev dB' : D.B' ⟶ D.T' := reducedClosedι _ _

lemma isClosed_preimage_range {Z : Scheme.{u}} (i : Z ⟶ M.T) [IsClosedImmersion i] :
    IsClosed (D.π.base ⁻¹' Set.range i.base) :=
  i.isClosedEmbedding.isClosed_range.preimage D.π.base.hom.continuous

/-- The complement `T' ∖ D'` lies over `O = T ∖ (G ∪ V)`. -/
lemma openComplement_dD'_le : D.dD'.openComplement ≤ D.π ⁻¹ᵁ M.O := by
  intro z hz
  have hcl : IsClosed (D.π.base ⁻¹' (Set.range M.a.base ∪ Set.range M.v.base)) := by
    rw [Set.preimage_union]
    exact (D.isClosed_preimage_range M.a).union (D.isClosed_preimage_range M.v)
  have hz' : z ∉ D.π.base ⁻¹' (Set.range M.a.base ∪ Set.range M.v.base) := by
    have : z ∉ Set.range D.dD'.base := hz
    rwa [range_reducedClosedι, hcl.closure_eq] at this
  simp only [Set.mem_preimage, Set.mem_union, not_or] at hz'
  exact ⟨hz'.1, hz'.2⟩

end AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum
