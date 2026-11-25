/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsionModels
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleExtFinite
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionComp

/-!

# Group actions on nearby cycles with finite coefficients factor through finite quotients

Let `M` be a model of finite type over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'`
separably closed), and `T` a finite discrete ring in which the characteristic exponent of `k'` is
invertible (and whose exponent is invertible in `k'`). A group `G` acting on the geometric model
`M.geometric` by morphisms of models over the identities (for instance the inertia group, through
the automorphisms of the geometric generic point, or the pro-`p` kernel of a change of trait)
acts on the nearby cycles `Ψ C` of a bounded constructible complex `C` of `T̲`-modules
(`NearbyCyclesModel.Hom.autAction`). This action factors through a finite quotient on cohomology
sheaves: a subgroup of finite index acts trivially on every `ℋ^q(Ψ C)`
(`NearbyCyclesModel.exists_finiteIndex_homology_autAction_eq_id_of_finite`).

Indeed `Ψ C` is bounded constructible (Deligne's finiteness theorem,
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_finite`), and the
endomorphisms of a constructible sheaf with finite coefficients on a separated scheme of finite
type over `k'` form a finite set (`AlgebraicGeometry.Etale.finite_hom_of_isConstructibleSheaf`,
transported to the condensed coefficients in
`ProEtale.CondensedRing.finite_homology_hom_of_boundedConstructible`). A group acting on finitely
many objects with finite endomorphism sets acts through a finite quotient
(`DerivedCategory.exists_finiteIndex_homology_map_eq_id`). No continuity of the action is needed.
The special fibre being of finite type over `k'`, this holds on all of it, in particular on its
quasi-compact opens.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **A group acting on a bounded complex with finite endomorphisms of its cohomology acts through
a finite quotient on cohomology**: let `K` be a complex with cohomology in `[a, b]` whose
cohomology objects have finitely many endomorphisms, and `act : G → End K` an action of a group
(`act 1 = 𝟙`, `act (g * h) = act h ≫ act g`). Then a subgroup of finite index acts trivially on
every `Hᵠ(K)`. -/
theorem exists_finiteIndex_homology_map_eq_id (K : DerivedCategory C) (a b : ℤ)
    (hab : ∀ q, q < a ∨ b < q → IsZero ((homologyFunctor C q).obj K))
    (hfin : ∀ q, Finite ((homologyFunctor C q).obj K ⟶ (homologyFunctor C q).obj K))
    {G : Type*} [Group G] (act : G → (K ⟶ K)) (h₁ : act 1 = 𝟙 K)
    (hmul : ∀ g h, act (g * h) = act h ≫ act g) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ ∀ g ∈ V, ∀ q, (homologyFunctor C q).map (act g) = 𝟙 _ := by
  let H (g : G) (q : ℤ) := (homologyFunctor C q).map (act g)
  have hH₁ (q : ℤ) : H 1 q = 𝟙 _ := by simp [H, h₁]
  have hHmul (g h : G) (q : ℤ) : H (g * h) q = H h q ≫ H g q := by simp [H, hmul]
  -- outside `[a, b]` the cohomology vanishes
  have hout (g : G) (q : ℤ) (hq : q < a ∨ b < q) : H g q = 𝟙 _ := (hab q hq).eq_of_src _ _
  let f : G → ∀ q : Finset.Icc a b, ((homologyFunctor C q).obj K ⟶ (homologyFunctor C q).obj K) :=
    fun g q ↦ H g q
  have hf (g : G) : f g = f 1 ↔ ∀ q, H g q = 𝟙 _ := by
    refine ⟨fun h q ↦ ?_, fun h ↦ funext fun q ↦ by simp [f, h, hH₁]⟩
    by_cases hq : q ∈ Finset.Icc a b
    · have := congrFun h ⟨q, hq⟩
      simpa [f, hH₁] using this
    · exact hout g q (by simp only [Finset.mem_Icc, not_and_or, not_le] at hq; omega)
  let V : Subgroup G :=
    { carrier := {g | ∀ q, H g q = 𝟙 _}
      one_mem' := hH₁
      mul_mem' := fun {g h} hg hh q ↦ by
        rw [hHmul, hg, hh, Category.comp_id]
      inv_mem' := fun {g} hg q ↦ by
        have := hHmul g g⁻¹ q
        rw [mul_inv_cancel, hH₁, hg q, Category.comp_id] at this
        exact this.symm }
  refine ⟨V, ?_, fun g hg ↦ hg⟩
  have key (g g' : G) : g⁻¹ * g' ∈ V ↔ f g = f g' := by
    rw [show (g⁻¹ * g' ∈ V) = ∀ q, H (g⁻¹ * g') q = 𝟙 _ from rfl]
    refine ⟨fun h ↦ funext fun q ↦ ?_, fun h q ↦ ?_⟩
    · have e₁ : H g' q = H (g * (g⁻¹ * g')) q := by rw [mul_inv_cancel_left]
      rw [hHmul, h q, Category.id_comp] at e₁
      exact e₁.symm
    · rw [hHmul]
      by_cases hq : q ∈ Finset.Icc a b
      · have := congrFun h ⟨q, hq⟩
        change H g q = H g' q at this
        rw [← this, ← hHmul, inv_mul_cancel, hH₁]
      · exact (hab q (by simp only [Finset.mem_Icc, not_and_or, not_le] at hq; omega)).eq_of_src _
          _
  have : Finite (G ⧸ V) := by
    let φ : G ⧸ V → ∀ q : Finset.Icc a b,
        ((homologyFunctor C q).obj K ⟶ (homologyFunctor C q).obj K) :=
      Quotient.lift f fun g g' (hgg' : _) ↦ (key g g').1 (QuotientGroup.leftRel_apply.1 hgg')
    refine Finite.of_injective φ fun x y hxy ↦ ?_
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 ((key _ _).2 hxy)
  exact Subgroup.finiteIndex_of_finite_quotient

end DerivedCategory

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- **A group acting on an object with finitely many endomorphisms acts through a finite
quotient**: for an action `act : G → End X` (`act 1 = 𝟙`, `act (g * h) = act h ≫ act g`)
on an object with finitely many endomorphisms, a subgroup of finite index acts as the identity. -/
theorem exists_finiteIndex_eq_id_of_finite_end (X : C) [Finite (X ⟶ X)] {G : Type*} [Group G]
    (act : G → (X ⟶ X)) (h₁ : act 1 = 𝟙 X) (hmul : ∀ g h, act (g * h) = act h ≫ act g) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ ∀ g ∈ V, act g = 𝟙 X := by
  let V : Subgroup G :=
    { carrier := {g | act g = 𝟙 X}
      one_mem' := h₁
      mul_mem' := fun {g h} hg hh ↦ by
        change act (g * h) = 𝟙 X
        rw [hmul, hg, hh, Category.comp_id]
      inv_mem' := fun {g} hg ↦ by
        have := hmul g g⁻¹
        rw [mul_inv_cancel, h₁, hg, Category.comp_id] at this
        exact this.symm }
  refine ⟨V, ?_, fun g hg ↦ hg⟩
  have key (g g' : G) : g⁻¹ * g' ∈ V ↔ act g = act g' := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have e₁ : act g' = act (g * (g⁻¹ * g')) := by rw [mul_inv_cancel_left]
      rw [hmul, show act (g⁻¹ * g') = 𝟙 X from h, Category.id_comp] at e₁
      exact e₁.symm
    · change act (g⁻¹ * g') = 𝟙 X
      rw [hmul, ← h, ← hmul, inv_mul_cancel, h₁]
  have : Finite (G ⧸ V) := by
    let φ : G ⧸ V → (X ⟶ X) :=
      _root_.Quotient.lift act fun g g' (hgg' : _) ↦
        (key g g').1 (QuotientGroup.leftRel_apply.1 hgg')
    refine Finite.of_injective φ fun x y hxy ↦ ?_
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 ((key _ _).2 hxy)
  exact Subgroup.finiteIndex_of_finite_quotient

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The cohomology sheaves of a bounded constructible complex with finite coefficients have
finitely many endomorphisms**, over a separated scheme of finite type over a separably closed
field: they are the condensed readings of constructible étale sheaves, and `ν^*` is fully
faithful (`AlgebraicGeometry.Etale.finite_hom_of_isConstructibleSheaf`). -/
theorem finite_homology_hom_of_boundedConstructible {k : Type u} [Field k] [IsSepClosed k]
    [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k))] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K)
    (q : ℤ) :
    Finite ((DerivedCategory.homologyFunctor _ q).obj K ⟶
      (DerivedCategory.homologyFunctor _ q).obj K) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} T)
  let Φ := finiteCoefficientModEquivalence X T
  obtain ⟨E, hE, ⟨e⟩⟩ := isEtaleOrigin_of_isConstructible T hK
  let F := (DerivedCategory.homologyFunctor _ q).obj E
  have : IsConstructibleSheaf F := hE.2 q
  have i₁ : Φ.functor.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (DerivedCategory.homologyFunctor _ q).obj
        ((finiteCoefficientDerivedEquivalence X T).functor.obj K) :=
    (Φ.functor.mapDerivedCategoryHomologyFunctorIso q).app K
  have i₂ : (DerivedCategory.homologyFunctor _ q).obj (D(ν^*(X)[A]).obj E) ≅ (ν^*(X)[A]).obj F :=
    (((ν^*(X)[A]).mapDerivedCategoryHomologyFunctorIso q).app E).symm
  have i : (DerivedCategory.homologyFunctor _ q).obj K ≅ Φ.inverse.obj ((ν^*(X)[A]).obj F) :=
    Φ.unitIso.app _ ≪≫ Φ.inverse.mapIso
      (i₁ ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso e.symm ≪≫ i₂)
  have := Etale.finite_hom_of_isConstructibleSheaf p F F
  exact Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful (ν^*(X)[A])).homEquiv.trans
    (Φ.symm.fullyFaithfulFunctor.homEquiv.trans (i.homCongr i).symm))

/-- **Morphisms between bounded constructible complexes with finite condensed coefficients form a
finite set**, over a separated scheme of finite type over a separably closed field: the complexes
are of étale origin, `ν^*` is fully faithful on bounded below complexes, and morphisms between
bounded constructible étale complexes form a finite set
(`AlgebraicGeometry.Etale.finite_hom_of_boundedConstructible`). -/
theorem finite_hom_of_boundedConstructible_of_finite {k : Type u} [Field k] [IsSepClosed k]
    [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k))] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) L) :
    Finite (K ⟶ L) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} T)
  obtain ⟨E, hE, ⟨e⟩⟩ := isEtaleOrigin_of_isConstructible T hK
  obtain ⟨E', hE', ⟨e'⟩⟩ := isEtaleOrigin_of_isConstructible T hL
  have := Etale.finite_hom_of_boundedConstructible p hE hE'
  let Φ := finiteCoefficientDerivedEquivalence X T
  exact Finite.of_equiv _ ((Equiv.ofBijective _
    (bijective_comparisonUpperStar_mapDerivedCategory_map E E' hE'.1.1)).trans
      ((e.homCongr e').trans (Φ.fullyFaithfulFunctor.homEquiv.symm)))

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] [IsSepClosed k']
  [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))] {p : ℕ} [Fact p.Prime]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- **Group actions on nearby cycles with finite coefficients factor through finite quotients**:
for a model `M` of finite type over the trait, a bounded constructible complex `C` of
`T̲`-modules, and a group `G` acting on `M.geometric` by morphisms of models over the identities
(`σ 1` with identity components, the components of `σ (g * h)` the composites of those of `σ g`
and `σ h`), a subgroup of finite index of `G` acts trivially on the cohomology sheaves of the
nearby cycles `Ψ C`. For the inertia group acting through the automorphisms of the geometric
generic point, this is the statement that the inertia action on the cohomology sheaves of the
nearby cycles factors through a finite quotient (SGA 7, Exp. XIII, 1.3), on the whole special
fibre, of finite type over `k'`. -/
theorem exists_finiteIndex_homology_autAction_eq_id_of_finite
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) M.total))}
    (hC : boundedConstructible _ C) {G : Type*} [Group G]
    (σ : G → M.geometric.Hom M.geometric (𝟙 M.total) (𝟙 X'.left))
    (h₁t : (σ 1).total = 𝟙 _) (h₁g : (σ 1).generic = 𝟙 _)
    (hmt : ∀ g h, (σ g).total ≫ (σ h).total = (σ (g * h)).total)
    (hmg : ∀ g h, (σ g).generic ≫ (σ h).generic = (σ (g * h)).generic) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ ∀ g ∈ V, ∀ q,
      (DerivedCategory.homologyFunctor _ q).map
        ((σ g).autAction (Profinite.continuousMapRingObj T) C) = 𝟙 _ := by
  obtain ⟨qM, -, _, _, _, -, hi⟩ := hM.exists_isPullback
  have : LocallyOfFiniteType X'.hom := MorphismProperty.of_isPullback hi ‹_›
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback hi ‹_›
  have : IsSeparated X'.hom := MorphismProperty.of_isPullback hi ‹_›
  have hΨ := boundedConstructible_geometricNearbyCycles_obj_of_finite T hp hpT M hM hC
  obtain ⟨⟨a, b, hab⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 hΨ
  exact DerivedCategory.exists_finiteIndex_homology_map_eq_id _ a b hab
    (finite_homology_hom_of_boundedConstructible T X'.hom hΨ) _
    ((σ 1).autAction_of_eq_id _ h₁t h₁g C)
    (fun g h ↦ (σ g).autAction_comp_of_eq _ (σ h) (σ (g * h)) (hmt g h) (hmg g h) C)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {k' : Type u} [Field k'] [IsSepClosed k']
  [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))] {p : ℕ} [Fact p.Prime]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- **Group actions on nearby cycles with finite coefficients factor through finite quotients, in
the derived category**: in the situation of
`NearbyCyclesModel.exists_finiteIndex_homology_autAction_eq_id_of_finite`, a subgroup of finite
index of `G` acts as the identity on the complex `Ψ C` itself, the endomorphisms of the bounded
constructible complex `Ψ C` forming a finite set
(`ProEtale.CondensedRing.finite_hom_of_boundedConstructible_of_finite`). -/
theorem exists_finiteIndex_autAction_eq_id_of_finite
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) M.total))}
    (hC : boundedConstructible _ C) {G : Type*} [Group G]
    (σ : G → M.geometric.Hom M.geometric (𝟙 M.total) (𝟙 X'.left))
    (h₁t : (σ 1).total = 𝟙 _) (h₁g : (σ 1).generic = 𝟙 _)
    (hmt : ∀ g h, (σ g).total ≫ (σ h).total = (σ (g * h)).total)
    (hmg : ∀ g h, (σ g).generic ≫ (σ h).generic = (σ (g * h)).generic) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ ∀ g ∈ V,
      (σ g).autAction (Profinite.continuousMapRingObj T) C = 𝟙 _ := by
  obtain ⟨qM, -, _, _, _, -, hi⟩ := hM.exists_isPullback
  have : LocallyOfFiniteType X'.hom := MorphismProperty.of_isPullback hi ‹_›
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback hi ‹_›
  have : IsSeparated X'.hom := MorphismProperty.of_isPullback hi ‹_›
  have hΨ := boundedConstructible_geometricNearbyCycles_obj_of_finite T hp hpT M hM hC
  have := finite_hom_of_boundedConstructible_of_finite T X'.hom hΨ hΨ
  exact exists_finiteIndex_eq_id_of_finite_end _ _ ((σ 1).autAction_of_eq_id _ h₁t h₁g C)
    (fun g h ↦ (σ g).autAction_comp_of_eq _ (σ h) (σ (g * h)) (hmt g h) (hmg g h) C)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
