/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.MoebiusDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductRetract

/-!
# Invariant retractions of the derived unit of a Galois tower are unique

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `K` a bounded
below complex of `Λ_X`-module objects such that, at every term, `g_{∞*} g_∞^* Kⁿ` is the colimit
of the finite levels and `g_∞^* Kⁿ` is `g_{∞*}`-acyclic. Given a Möbius decomposition `D` of
`M∞ = g_{∞*} g_∞^* K` (`AlgebraicGeometry.ProEtale.GaloisTower.MoebiusDecomposition`), two
retractions `R, R'` of the derived unit `K ⟶ Rg_{∞*} Lg_∞^* K` which are invariant under the
derived unit transports along the automorphisms `D.σ i a` are equal
(`AlgebraicGeometry.ProEtale.GaloisTower.MoebiusDecomposition.eq_of_retraction_derivedUnit`,
and `..._of_iso` for an object of the derived category isomorphic to `K`): there are no phantom
invariant maps.

## Proof

Through `CategoryTheory.Adjunction.derivedUnitIso : M∞ ≅ Rg_{∞*} Lg_∞^* K`, the difference
`R - R'` becomes a morphism `δ : Q(M∞) ⟶ Q(K)` killed by the unit `u : K ⟶ M∞` and invariant
under the actions of the `D.σ i a`. We write `M∞` as a retract of the coproduct `∐ᵢ M∞`
(`GaloisTower.MoebiusDecomposition.sigmaSection_comp_sigmaRetraction`): the section has
components `|Aᵢ|⁻¹ eᵢ` (resp. `e_{i₀}`), defined termwise on the colimit of the finite levels
where they form finite sums, and the retraction has components
`cᵢ = |Aᵢ| - ∑ₐ σ i a` (resp. `τ ≫ u`). Each `Q(cᵢ) ≫ δ` vanishes, hence so does `δ`, since
`Q` sends coproducts of complexes to coproducts
(`DerivedCategory.eq_zero_of_Q_map_inj_comp_comp_eq_zero`).
-/

@[expose] public section

-- several declarations do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

/-- An inverse of a multiplication by an integer commutes with every morphism. -/
lemma inv_nsmul_id_comp {C : Type*} [Category* C] [Preadditive C] {N N' : C} (k : ℕ)
    [IsIso (k • 𝟙 N)] [IsIso (k • 𝟙 N')] (f : N ⟶ N') :
    inv (k • 𝟙 N) ≫ f = f ≫ inv (k • 𝟙 N') := by
  rw [IsIso.inv_comp_eq, ← assoc, IsIso.eq_comp_inv, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, id_comp, comp_id]

/-- A morphism `δ` fixed by the images `F(aₐ)` of finitely many endomorphisms is killed by
`F(k - ∑ₐ aₐ)`, where `k` is their number. -/
lemma map_nsmul_id_sub_sum_comp_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {α : Type*} [Fintype α] {M : C} {Y : D}
    (act : α → (M ⟶ M)) (δ : F.obj M ⟶ Y) (h : ∀ a, F.map (act a) ≫ δ = δ) :
    F.map (Fintype.card α • 𝟙 M - ∑ a, act a) ≫ δ = 0 := by
  rw [F.map_sub, F.map_nsmul, F.map_sum, Preadditive.sub_comp, Preadditive.sum_comp,
    CategoryTheory.Functor.map_id, Preadditive.nsmul_comp, id_comp]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, sub_self]

/-- The terms of a finite sum of morphisms of complexes. -/
lemma homologicalComplex_sum_f {C : Type*} [Category* C] [Preadditive C] {ι α : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (s : Finset α) (f : α → (K ⟶ L)) (n : ι) :
    (∑ a ∈ s, f a).f n = ∑ a ∈ s, (f a).f n :=
  map_sum (HomologicalComplex.Hom.fAddMonoidHom n) f s

/-- If `s` inverts `k` and commutes with `e`, and the endomorphisms `aₐ` sum to zero after `e`,
then `e ≫ s ≫ (k - ∑ₐ aₐ) = e`. -/
lemma e_comp_comp_sub_sum_eq {C : Type*} [Category* C] [Preadditive C] {α : Type*} [Fintype α]
    {B : C} (k : ℕ) (e s : B ⟶ B) (hs : s ≫ (k • 𝟙 B) = 𝟙 B) (hes : e ≫ s = s ≫ e)
    (act : α → (B ⟶ B)) (h : ∑ a, e ≫ act a = 0) :
    e ≫ s ≫ (k • 𝟙 B - ∑ a, act a) = e := by
  rw [Preadditive.comp_sub, Preadditive.comp_sub, hs, comp_id, ← assoc, hes, assoc,
    Preadditive.comp_sum, h, comp_zero, sub_zero]

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] {T : GaloisTower ginf}
  {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N)}
  {K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ}
  {hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n))}

-- the complex `M∞ = g_{∞*} g_∞^* K`
set_option quotPrecheck false in
local notation "M∞" => (((ginf)^*⟦Λ⟧ ⋙ (ginf)_*⟦Λ⟧).mapHomologicalComplex _).obj K

namespace MoebiusDecomposition

variable (D : T.MoebiusDecomposition Λ hd K hc)

/-! ### Locally finite sums -/

section LocallyFinite

variable {n : ℤ} {Z : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X)} (g : D.ι → ((infFunctor Λ ginf).obj (K.X n) ⟶ Z))

/-- The finite sum `∑_{i ∈ F j} eᵢ ≫ gᵢ` on the finite level `j`. -/
noncomputable def levelSum (j : T.J) : (T.levelFunctor Λ j).obj (K.X n) ⟶ Z :=
  ∑ i ∈ D.F j, T.infTransport Λ (K.X n) j ≫ D.e i n ≫ g i

/-- A sum over a finite set outside of which the terms vanish computes `levelSum`. -/
lemma sum_eq_levelSum (j : T.J) (S : Finset D.ι)
    (hS : ∀ i, i ∉ S → T.infTransport Λ (K.X n) j ≫ D.e i n = 0) :
    ∑ i ∈ S, T.infTransport Λ (K.X n) j ≫ D.e i n ≫ g i = D.levelSum g j := by
  classical
  have h₁ := Finset.sum_subset (Finset.subset_union_left (s₂ := D.F j))
    (f := fun i ↦ T.infTransport Λ (K.X n) j ≫ D.e i n ≫ g i)
    (fun i _ hi ↦ by rw [← assoc, hS i hi, zero_comp])
  have h₂ := Finset.sum_subset (Finset.subset_union_right (s₁ := S))
    (f := fun i ↦ T.infTransport Λ (K.X n) j ≫ D.e i n ≫ g i)
    (fun i _ hi ↦ by rw [← assoc, D.infTransport_comp_eq_zero j n i hi, zero_comp])
  exact h₁.trans h₂.symm

/-- The finite sums are compatible with the transition maps. -/
lemma transport_comp_levelSum {j j' : T.J} (h : j ≤ j') :
    T.transport Λ (K.X n) h ≫ D.levelSum g j' = D.levelSum g j := by
  rw [levelSum, Preadditive.comp_sum]
  simp_rw [← assoc, T.transport_comp_infTransport]
  simp_rw [assoc]
  refine D.sum_eq_levelSum g j _ fun i hi ↦ ?_
  rw [← T.transport_comp_infTransport Λ (K.X n) h, assoc, D.infTransport_comp_eq_zero j' n i hi,
    comp_zero]

/-- The cocone of the finite sums `∑_{i ∈ F j} eᵢ ≫ gᵢ`. -/
noncomputable def levelSumCocone : Cocone (T.moduleDiagram Λ (K.X n)) where
  pt := Z
  ι :=
    { app j := D.levelSum g j
      naturality _ _ f := (D.transport_comp_levelSum g (leOfHom f)).trans (comp_id _).symm }

/-- The locally finite sum `∑ᵢ eᵢ ≫ gᵢ : g_{∞*} g_∞^* Kⁿ ⟶ Z`, glued from the finite sums on the
finite levels. -/
noncomputable def sumDesc : (infFunctor Λ ginf).obj (K.X n) ⟶ Z :=
  (hc n).desc (D.levelSumCocone g)

/-- On the finite level `j`, `sumDesc` is the finite sum `levelSum`. -/
lemma infTransport_comp_sumDesc (j : T.J) :
    T.infTransport Λ (K.X n) j ≫ D.sumDesc g = D.levelSum g j :=
  (hc n).fac (D.levelSumCocone g) j

/-- Composing a locally finite sum with a morphism. -/
lemma sumDesc_comp {Z' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : Z ⟶ Z') :
    D.sumDesc g ≫ φ = D.sumDesc (fun i ↦ g i ≫ φ) := by
  refine (hc n).hom_ext fun j ↦ ?_
  change T.infTransport Λ (K.X n) j ≫ _ = T.infTransport Λ (K.X n) j ≫ _
  rw [← assoc, infTransport_comp_sumDesc, infTransport_comp_sumDesc, levelSum, levelSum,
    Preadditive.sum_comp]
  simp only [assoc]

/-- The locally finite sum `∑ᵢ eᵢ ≫ gᵢ` is the identity if every `eᵢ ≫ gᵢ = eᵢ`. -/
lemma sumDesc_eq_id
    (g : D.ι → ((infFunctor Λ ginf).obj (K.X n) ⟶ (infFunctor Λ ginf).obj (K.X n)))
    (hg : ∀ i, D.e i n ≫ g i = D.e i n) : D.sumDesc g = 𝟙 _ := by
  refine (hc n).hom_ext fun j ↦ ?_
  change T.infTransport Λ (K.X n) j ≫ _ = T.infTransport Λ (K.X n) j ≫ _
  rw [infTransport_comp_sumDesc, levelSum, comp_id]
  simp_rw [hg]
  rw [← Preadditive.comp_sum, D.infTransport_comp_sum]

/-- The differentials pass through locally finite sums. -/
lemma map_d_comp_sumDesc {m : ℤ}
    (g : D.ι → ((infFunctor Λ ginf).obj (K.X m) ⟶ Z)) :
    (infFunctor Λ ginf).map (K.d n m) ≫ D.sumDesc g =
      D.sumDesc (fun i ↦ (infFunctor Λ ginf).map (K.d n m) ≫ g i) := by
  refine (hc n).hom_ext fun j ↦ ?_
  change T.infTransport Λ (K.X n) j ≫ _ = T.infTransport Λ (K.X n) j ≫ _
  rw [infTransport_comp_sumDesc, ← assoc, T.infTransport_naturality, assoc,
    infTransport_comp_sumDesc, levelSum, levelSum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← assoc, ← T.infTransport_naturality, assoc, ← assoc (D.e i n), D.comm i n m, assoc]

end LocallyFinite

/-! ### `M∞` as a retract of a coproduct -/

open Classical in
/-- The normalizing scalar of the `i`-th component: `|Aᵢ|⁻¹` for `i ≠ i₀`, and `1` for `i₀`. -/
noncomputable def scal (i : D.ι) (n : ℤ) :
    (infFunctor Λ ginf).obj (K.X n) ⟶ (infFunctor Λ ginf).obj (K.X n) :=
  if i = D.i₀ then 𝟙 _ else
    haveI := D.card i ((infFunctor Λ ginf).obj (K.X n))
    inv (Fintype.card (D.A i) • 𝟙 _)

/-- The normalizing scalars commute with all morphisms. -/
lemma scal_comm (i : D.ι) {n m : ℤ}
    (f : (infFunctor Λ ginf).obj (K.X n) ⟶ (infFunctor Λ ginf).obj (K.X m)) :
    D.scal i n ≫ f = f ≫ D.scal i m := by
  unfold scal
  split_ifs
  · rw [id_comp, comp_id]
  · have := D.card i ((infFunctor Λ ginf).obj (K.X n))
    have := D.card i ((infFunctor Λ ginf).obj (K.X m))
    exact inv_nsmul_id_comp _ f

/-- For `i ≠ i₀`, the normalizing scalar inverts `|Aᵢ|`. -/
lemma scal_comp_nsmul_of_ne (i : D.ι) (hi : i ≠ D.i₀) (n : ℤ) :
    D.scal i n ≫ (Fintype.card (D.A i) • 𝟙 _) = 𝟙 _ := by
  have := D.card i ((infFunctor Λ ginf).obj (K.X n))
  rw [scal, ite_eq_right hi]
  exact IsIso.inv_hom_id _

/-- The coproduct `∐ᵢ M∞` of complexes, computed termwise. -/
noncomputable def cofan : Cofan (fun _ : D.ι ↦ M∞) :=
  let mkCofan {C : Type (u + 2)} [Category.{u + 1} C] [HasZeroMorphisms C]
      [HasColimitsOfShape (Discrete D.ι) C] (N : CochainComplex C ℤ) :
      Cofan (fun _ : D.ι ↦ N) :=
    HomologicalComplex.coconeOfHasColimitEval (Discrete.functor fun _ : D.ι ↦ N)
  haveI : HasColimitsOfShape (Discrete D.ι)
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    inferInstance
  mkCofan M∞

/-- The cofan `MoebiusDecomposition.cofan` is a coproduct. -/
noncomputable def isColimitCofan : IsColimit D.cofan :=
  let mkIsColimit {C : Type (u + 2)} [Category.{u + 1} C] [HasZeroMorphisms C]
      [HasColimitsOfShape (Discrete D.ι) C] (N : CochainComplex C ℤ) :
      IsColimit (HomologicalComplex.coconeOfHasColimitEval
        (Discrete.functor fun _ : D.ι ↦ N)) :=
    HomologicalComplex.isColimitCoconeOfHasColimitEval _
  haveI : HasColimitsOfShape (Discrete D.ι)
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    inferInstance
  mkIsColimit M∞

/-- The section `M∞ ⟶ ∐ᵢ M∞` with components `|Aᵢ|⁻¹ eᵢ` (`i ≠ i₀`) and `e_{i₀}`. -/
noncomputable def sigmaSection : M∞ ⟶ D.cofan.pt where
  f n := D.sumDesc (fun i ↦ D.scal i n ≫ (D.cofan.inj i).f n)
  comm' n m _ := by
    change D.sumDesc _ ≫ _ = (infFunctor Λ ginf).map (K.d n m) ≫ _
    rw [sumDesc_comp, map_d_comp_sumDesc]
    congr 1
    funext i
    rw [assoc, (D.cofan.inj i).comm n m, ← assoc, D.scal_comm i, assoc]
    rfl

/-! ### The retraction, for an abstract family of actions

To keep the terms small, the actions of the `σ i a` on `M∞` are an arbitrary family `act` of
endomorphisms which are termwise `GaloisTower.infAction`; it is specialized to the unit transports
only at the end. -/

section Action

open Classical in
/-- The components of the retraction `∐ᵢ M∞ ⟶ M∞`: `|Aᵢ| - ∑ₐ σ i a` for `i ≠ i₀`, and the
invariant projector `τ ≫ u` for `i₀`. -/
noncomputable def component (act : ∀ i, D.A i → (M∞ ⟶ M∞)) (i : D.ι) : M∞ ⟶ M∞ :=
  if i = D.i₀ then
    T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K
  else Fintype.card (D.A i) • 𝟙 _ - ∑ a, act i a

/-- The terms of the component `τ ≫ u` at `i₀`. -/
lemma component_i₀_f (act : ∀ i, D.A i → (M∞ ⟶ M∞)) (n : ℤ) :
    (D.component act D.i₀).f n =
      T.trace Λ (K.X n) hd (hc n) ≫ (infUnit Λ ginf).app (K.X n) := by
  unfold component
  rw [ite_eq_left rfl, HomologicalComplex.comp_f,
    Adjunction.mapHomologicalComplex_unit_app_f]
  rfl

/-- The components at `i ≠ i₀`. -/
lemma component_of_ne (act : ∀ i, D.A i → (M∞ ⟶ M∞)) (i : D.ι) (hi : i ≠ D.i₀) :
    D.component act i = Fintype.card (D.A i) • 𝟙 M∞ - ∑ a, act i a := by
  unfold component
  rw [ite_eq_right hi]

/-- The component `eᵢ` on the `n`-th term of `M∞`. -/
noncomputable def eF (i : D.ι) (n : ℤ) : (M∞).X n ⟶ (M∞).X n := D.e i n

/-- The normalizing scalar on the `n`-th term of `M∞`. -/
noncomputable def sF (i : D.ι) (n : ℤ) : (M∞).X n ⟶ (M∞).X n := D.scal i n

/-- For `i ≠ i₀`, the normalizing scalar inverts `|Aᵢ|` (on the terms of `M∞`). -/
lemma sF_comp_nsmul (i : D.ι) (hi : i ≠ D.i₀) (n : ℤ) :
    D.sF i n ≫ (Fintype.card (D.A i) • 𝟙 ((M∞).X n)) = 𝟙 _ :=
  D.scal_comp_nsmul_of_ne i hi n

/-- The normalizing scalar commutes with `eᵢ` (on the terms of `M∞`). -/
lemma eF_comp_sF (i : D.ι) (n : ℤ) : D.eF i n ≫ D.sF i n = D.sF i n ≫ D.eF i n :=
  (D.scal_comm i (D.e i n)).symm

/-- On the `i`-th component (`i ≠ i₀`), the sum of the actions of the `σ i a` vanishes. -/
lemma sum_eF_comp_act_f (act : ∀ i, D.A i → (M∞ ⟶ M∞))
    (hact : ∀ i a n, (act i a).f n = infAction Λ (K.X n) (D.σ i a) (D.hσ i a))
    (i : D.ι) (hi : i ≠ D.i₀) (n : ℤ) :
    ∑ a, D.eF i n ≫ (act i a).f n = 0 :=
  (Finset.sum_congr rfl fun a _ ↦ congrArg (D.eF i n ≫ ·) (hact i a n)).trans
    (D.sum_comp_infAction i hi n)

/-- For `i ≠ i₀`, the normalized component `|Aᵢ|⁻¹ eᵢ` is split by `|Aᵢ| - ∑ₐ σ i a`. -/
lemma eF_comp_sF_comp_component_f (act : ∀ i, D.A i → (M∞ ⟶ M∞))
    (hact : ∀ i a n, (act i a).f n = infAction Λ (K.X n) (D.σ i a) (D.hσ i a))
    (i : D.ι) (hi : i ≠ D.i₀) (n : ℤ) :
    D.eF i n ≫ D.sF i n ≫ (D.component act i).f n = D.eF i n := by
  rw [component_of_ne D act i hi, HomologicalComplex.sub_f_apply,
    HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f, homologicalComplex_sum_f]
  exact e_comp_comp_sub_sum_eq (Fintype.card (D.A i)) (D.eF i n) (D.sF i n)
    (D.sF_comp_nsmul i hi n) (D.eF_comp_sF i n) (fun a ↦ (act i a).f n)
    (D.sum_eF_comp_act_f act hact i hi n)

/-- Each normalized component of the section is split by the corresponding component of the
retraction. -/
lemma e_comp_scal_comp_component_f (act : ∀ i, D.A i → (M∞ ⟶ M∞))
    (hact : ∀ i a n, (act i a).f n = infAction Λ (K.X n) (D.σ i a) (D.hσ i a)) (i : D.ι) (n : ℤ) :
    D.e i n ≫ D.scal i n ≫ (D.component act i).f n = D.e i n := by
  by_cases hi : i = D.i₀
  · subst hi
    rw [component_i₀_f, scal, ite_eq_left rfl, id_comp, D.e_i₀, assoc,
      ← assoc ((infUnit Λ ginf).app (K.X n)), T.unit_comp_trace]
    erw [id_comp]
  · exact D.eF_comp_sF_comp_component_f act hact i hi n

/-- The retraction `∐ᵢ M∞ ⟶ M∞` with components `MoebiusDecomposition.component`. -/
noncomputable def sigmaRetraction (act : ∀ i, D.A i → (M∞ ⟶ M∞)) : D.cofan.pt ⟶ M∞ :=
  Cofan.IsColimit.desc D.isColimitCofan (D.component act)

/-- The components of the retraction `∐ᵢ M∞ ⟶ M∞`. -/
lemma inj_comp_sigmaRetraction (act : ∀ i, D.A i → (M∞ ⟶ M∞)) (i : D.ι) :
    D.cofan.inj i ≫ D.sigmaRetraction act = D.component act i :=
  Cofan.IsColimit.fac D.isColimitCofan (D.component act) i

/-- **`M∞` is a retract of `∐ᵢ M∞`**, through the locally finite decomposition `∑ᵢ eᵢ = 𝟙`. -/
lemma sigmaSection_comp_sigmaRetraction (act : ∀ i, D.A i → (M∞ ⟶ M∞))
    (hact : ∀ i a n, (act i a).f n = infAction Λ (K.X n) (D.σ i a) (D.hσ i a)) :
    D.sigmaSection ≫ D.sigmaRetraction act = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change D.sumDesc _ ≫ _ = _
  rw [sumDesc_comp]
  refine D.sumDesc_eq_id _ fun i ↦ ?_
  rw [assoc, ← HomologicalComplex.comp_f, inj_comp_sigmaRetraction]
  exact D.e_comp_scal_comp_component_f act hact i n

/-- **No phantom maps out of `M∞`.** Two morphisms `δ₁ δ₂ : Q(M∞) ⟶ Y` which agree after the
invariant projector `τ ≫ u` and are fixed by the actions of the `σ i a` are equal. -/
lemma eq_of_comp_eq (act : ∀ i, D.A i → (M∞ ⟶ M∞))
    (hact : ∀ i a n, (act i a).f n = infAction Λ (K.X n) (D.σ i a) (D.hσ i a)) (Y : DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (δ₁ δ₂ : DerivedCategory.Q.obj M∞ ⟶ Y)
    (hu : DerivedCategory.Q.map (T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K) ≫
        δ₁ = DerivedCategory.Q.map (T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K) ≫
        δ₂)
    (hδ₁ : ∀ i a, DerivedCategory.Q.map (act i a) ≫ δ₁ = δ₁)
    (hδ₂ : ∀ i a, DerivedCategory.Q.map (act i a) ≫ δ₂ = δ₂) : δ₁ = δ₂ := by
  refine DerivedCategory.eq_of_Q_map_inj_comp_comp_eq D.isColimitCofan
    D.sigmaSection (D.sigmaRetraction act) (D.sigmaSection_comp_sigmaRetraction act hact) δ₁ δ₂
    fun i ↦ ?_
  rw [inj_comp_sigmaRetraction]
  by_cases hi : i = D.i₀
  · rw [component, ite_eq_left hi]
    exact hu
  · rw [component_of_ne D act i hi]
    exact (map_nsmul_id_sub_sum_comp_eq_zero DerivedCategory.Q (act i) δ₁ (hδ₁ i)).trans
      (map_nsmul_id_sub_sum_comp_eq_zero DerivedCategory.Q (act i) δ₂ (hδ₂ i)).symm

end Action

/-! ### Uniqueness of invariant retractions -/

/-- The terms of the endomorphism of `M∞` induced by an endomorphism `α` of `g_{∞*} g_∞^*`. -/
lemma mapHomologicalComplex_app_f_aux
    (α : (ginf)^*⟦Λ⟧ ⋙ (ginf)_*⟦Λ⟧ ⟶ (ginf)^*⟦Λ⟧ ⋙ (ginf)_*⟦Λ⟧) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex α _).app K).f n = α.app (K.X n) :=
  NatTrans.mapHomologicalComplex_app_f α _ K n

/-- The unit transport along an automorphism `σ` of `Y_∞` over `X`, applied termwise to `M∞`, is
`GaloisTower.infAction`. -/
lemma unitTransport_app_f (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K).f n =
      infAction Λ (K.X n) σ hσ :=
  (mapHomologicalComplex_app_f_aux _ n).trans (infAction_eq Λ (K.X n) σ hσ).symm

section Derived

variable (a : ℤ) [K.IsStrictlyGE a]
  (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
  {R : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj (DerivedCategory.Q.obj K)) ⟶
    DerivedCategory.Q.obj K}

include hK in
/-- A retraction `R` of the derived unit, read on `M∞`, is a retraction of the levelwise unit. -/
lemma Q_map_unit_comp_derivedUnitIso_hom_comp
    (hR : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app _ ≫ R = 𝟙 _) :
    DerivedCategory.Q.map
      (((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K) ≫
      (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom ≫ R = 𝟙 _ := by
  have hU : DerivedCategory.Q.map
      (((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K) ≫
      (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
        (DerivedCategory.Q.obj K) :=
    Adjunction.Q_map_unit_comp_derivedUnitIso_hom K a hK _
  rw [← assoc, hU]
  exact hR

include hK in
/-- A retraction `R` of the derived unit, read on `M∞`, is a retraction of the levelwise unit,
composed with the levelwise trace. -/
lemma Q_map_complexTrace_comp_unit_comp_derivedUnitIso_hom_comp
    (hR : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app _ ≫ R = 𝟙 _) :
    DerivedCategory.Q.map (T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K) ≫
      (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom ≫ R =
        DerivedCategory.Q.map (T.complexTrace Λ hd K hc) := by
  rw [Functor.map_comp, assoc, Q_map_unit_comp_derivedUnitIso_hom_comp a hK hR]
  exact comp_id _

include hK in
/-- A retraction of the derived unit invariant under the unit transport along `σ`, read on `M∞`,
is invariant under the levelwise unit transport. -/
lemma comp_derivedUnitIso_hom_comp (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf)
    (φ : DerivedCategory.Q.obj M∞ ⟶ DerivedCategory.Q.obj M∞)
    (hφ : (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom ≫
        derivedUnitTransport Λ σ hσ hσ (DerivedCategory.Q.obj K) =
      φ ≫ (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom)
    (hinv : derivedUnitTransport Λ σ hσ hσ (DerivedCategory.Q.obj K) ≫ R = R) :
    φ ≫ (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom ≫ R =
      (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom ≫ R := by
  rw [← assoc, ← hφ, assoc, hinv]

end Derived

/-- **Invariant retractions of the derived unit of a Galois tower are unique.** Given a Möbius
decomposition of `g_{∞*} g_∞^* K` for a bounded below complex `K` such that every `g_∞^* Kⁿ` is
`g_{∞*}`-acyclic, two retractions of the derived unit `K ⟶ Rg_{∞*} Lg_∞^* K` invariant under the
derived unit transports along the automorphisms `D.σ i a` are equal. -/
theorem eq_of_retraction_derivedUnit (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
    {R R' : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj (DerivedCategory.Q.obj K)) ⟶
      DerivedCategory.Q.obj K}
    (hR : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app _ ≫ R = 𝟙 _)
    (hR' : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app _ ≫ R' = 𝟙 _)
    (hinv : ∀ i a, derivedUnitTransport Λ (D.σ i a) (D.hσ i a) (D.hσ i a)
      (DerivedCategory.Q.obj K) ≫ R = R)
    (hinv' : ∀ i a, derivedUnitTransport Λ (D.σ i a) (D.hσ i a) (D.hσ i a)
      (DerivedCategory.Q.obj K) ≫ R' = R') :
    R = R' := by
  have h := D.eq_of_comp_eq _ (fun i b n ↦ unitTransport_app_f (D.σ i b) (D.hσ i b) n) _ _ _
    ((Q_map_complexTrace_comp_unit_comp_derivedUnitIso_hom_comp a hK hR).trans
      (Q_map_complexTrace_comp_unit_comp_derivedUnitIso_hom_comp a hK hR').symm)
    (fun i b ↦ comp_derivedUnitIso_hom_comp a hK (D.σ i b) (D.hσ i b) _
      (derivedUnitIso_hom_comp_derivedUnitTransport_self Λ ginf (D.σ i b) (D.hσ i b) K a hK)
      (hinv i b))
    (fun i b ↦ comp_derivedUnitIso_hom_comp a hK (D.σ i b) (D.hσ i b) _
      (derivedUnitIso_hom_comp_derivedUnitTransport_self Λ ginf (D.σ i b) (D.hσ i b) K a hK)
      (hinv' i b))
  exact (cancel_epi _).1 h

/-- `MoebiusDecomposition.eq_of_retraction_derivedUnit` for an object `C ≅ K` of the derived
category. -/
theorem eq_of_retraction_derivedUnit_of_iso (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
    {C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (e : DerivedCategory.Q.obj K ≅ C)
    {R R' : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C) ⟶ C}
    (hR : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C ≫ R = 𝟙 _)
    (hR' : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C ≫ R' = 𝟙 _)
    (hinv : ∀ i a, derivedUnitTransport Λ (D.σ i a) (D.hσ i a) (D.hσ i a) C ≫ R = R)
    (hinv' : ∀ i a, derivedUnitTransport Λ (D.σ i a) (D.hσ i a) (D.hσ i a) C ≫ R' = R') :
    R = R' := by
  have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.naturality e.hom
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
  have key (S : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C) ⟶ C)
      (hS : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C ≫ S = 𝟙 _)
      (hSi : ∀ i a, derivedUnitTransport Λ (D.σ i a) (D.hσ i a) (D.hσ i a) C ≫ S = S) :
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app _ ≫
          (R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.hom) ≫ S ≫ e.inv) = 𝟙 _ ∧
        ∀ i a, derivedUnitTransport Λ (D.σ i a) (D.hσ i a) (D.hσ i a)
          (DerivedCategory.Q.obj K) ≫
            (R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.hom) ≫ S ≫ e.inv) =
          R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.hom) ≫ S ≫ e.inv := by
    refine ⟨?_, fun i b ↦ ?_⟩
    · rw [← reassoc_of% hn, reassoc_of% hS, Iso.hom_inv_id]
      rfl
    · rw [← reassoc_of% (derivedUnitTransport_naturality Λ (D.σ i b) (D.hσ i b) (D.hσ i b) e.hom),
        reassoc_of% (hSi i b)]
  obtain ⟨h₁, h₂⟩ := key R hR hinv
  obtain ⟨h₁', h₂'⟩ := key R' hR' hinv'
  have h := D.eq_of_retraction_derivedUnit a hK h₁ h₁' h₂ h₂'
  rwa [cancel_epi, cancel_mono] at h

end MoebiusDecomposition

end AlgebraicGeometry.ProEtale.GaloisTower
