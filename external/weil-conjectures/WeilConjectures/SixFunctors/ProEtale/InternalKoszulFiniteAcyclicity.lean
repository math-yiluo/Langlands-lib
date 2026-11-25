/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import all WeilConjectures.AlgebraicGeometry.CompletionTriangleComparison
import WeilConjectures.SixFunctors.ProEtale.InternalKoszulConeCoordinates

/-! # Acyclicity of one normalized finite singleton augmentation

Source: Stacks Project, More on Algebra, Tag 062F; algebraization.tex,
Lemma derived-completion-koszul (0A0E); proetale.tex, Section 099L.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
private theorem map_cone_hom_ext {A B : Type*} [Category A] [Abelian A]
    [Category B] [Preadditive B] (F : A ⥤ B) [F.Additive]
    {P Q : CochainComplex A ℤ} (s : P ⟶ Q) (q : ℤ) {Y : B}
    {f g : F.obj ((CochainComplex.mappingCone s).X q) ⟶ Y}
    (hl : F.map ((CochainComplex.mappingCone.inl s).v (q + 1) q (by omega)) ≫ f =
      F.map ((CochainComplex.mappingCone.inl s).v (q + 1) q (by omega)) ≫ g)
    (hr : F.map ((CochainComplex.mappingCone.inr s).f q) ≫ f =
      F.map ((CochainComplex.mappingCone.inr s).f q) ≫ g) : f = g := by
  have hid := congrArg F.map (CochainComplex.mappingCone.id_X s q (q + 1) rfl)
  simp only [Functor.map_add, Functor.map_comp] at hid
  calc
    f = (F.map ((CochainComplex.mappingCone.fst s).1.v q (q + 1) rfl) ≫
          F.map ((CochainComplex.mappingCone.inl s).v (q + 1) q (by omega)) +
        F.map ((CochainComplex.mappingCone.snd s).v q q (add_zero q)) ≫
          F.map ((CochainComplex.mappingCone.inr s).f q)) ≫ f := by
      rw [hid, F.map_id, Category.id_comp]
    _ = (F.map ((CochainComplex.mappingCone.fst s).1.v q (q + 1) rfl) ≫
          F.map ((CochainComplex.mappingCone.inl s).v (q + 1) q (by omega)) +
        F.map ((CochainComplex.mappingCone.snd s).v q q (add_zero q)) ≫
          F.map ((CochainComplex.mappingCone.inr s).f q)) ≫ g := by
      simp only [Preadditive.add_comp, Category.assoc, hl, hr]
    _ = g := by rw [hid, F.map_id, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- A single finite augmentation, normalized on degree zero and zero on every other
Koszul summand, is a quasi-isomorphism on a K-flat complex. No transition maps or
inverse limits occur in this assertion.

Source: Stacks Project, More on Algebra, Tag 062F; algebraization.tex,
Lemma derived-completion-koszul (0A0E); proetale.tex, Section 099L.
(auxiliary; not a blueprint node).

Proof: the constant uniformizer pi is regular, and exact inverse image preserves its
injective multiplication map. Since a and pi generate the same ideal sheaf, locally
a=u*pi and pi=v*a. Injectivity of multiplication by pi gives vu=1; commutativity
therefore makes u a unit. Thus a^(n+1) is also regular and has the same principal
ideal as pi^(n+1). The negative two-term singleton complex consequently resolves the
constant finite quotient, by the regular-sequence Koszul argument of Tag 062F.
The constant-to-continuous coefficient map is flat and has these same finite
quotients, so extension gives a resolution of the actual finite coefficient module.
The point coefficient isomorphism fixes its identification with the specified
continuous coefficient object. Tensor this coefficient resolution by the actual
K-flat P. K-flatness makes its augmentation a quasi-isomorphism, including for
unbounded P. Exact scalar restriction and the section equivalence preserve this
quasi-isomorphism and identify its source with the displayed total tensor complex.
In Koszul degree zero the dual unit is the identification with the rank-one ring;
thus the unit equation specifies the augmentation on every summand (p,0).
The vanishing hypothesis specifies it on all other summands. Joint epimorphy of
the total-tensor coproduct inclusions identifies v with that tensor augmentation.
No termwise flatness of P is needed. Zero P and the empty scheme give acyclic zero
complexes, so they satisfy the same conclusion. -/
theorem koszul_finite_augmentation_quasiIso [IsNoetherian X]
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      IsRingedIdealGeneratingList (ring l E X)
        (ConstantCompletion.kernelIdeal (residue l E X)).module
        (ConstantCompletion.kernelIdeal (residue l E X)).inclusion U 1
        (fun _ ↦ a.val (op U)))
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P)
    (n : ℕ)
    (v : ((ringedKoszulTensorTower (ring l E X) 1 (fun _ ↦ a)).obj
        (complex l E X P)).obj (op n) ⟶ (quotients l E X P).obj (op n))
    (hu : ringedKoszulTensorUnitComponent (ring l E X) 1 (fun _ ↦ a)
        (complex l E X P) (op n) ≫ v = (quotientUnits l E X P).app (op n))
    (hz : ∀ p j : ℤ, j ≠ 0 →
      HomologicalComplex.ιMapBifunctor (complex l E X P)
          ((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n))
          (curriedTensor _) (.up ℤ) p j (p + j) rfl ≫ v.f (p + j) = 0) :
    QuasiIso v := by
  obtain ⟨data, hdata⟩ := PrincipalReduction.principalReductionConeData l E X
  obtain ⟨e, he₀, he₁⟩ := koszul_uniformizer_cone_coordinates l E X a ha data.d
    (fun S b s ↦ (hdata S b s).1) P n
  let F := modules l E X
  let G := F.mapHomologicalComplex (.up ℤ)
  let s := PrincipalReduction.scalar l E X data.d n P
  let c : CochainComplex.mappingCone s ⟶ (AdicCompletion.level l E X n).obj P :=
    CochainComplex.mappingCone.descShortComplex
      (ShortComplex.mk s (AdicCompletion.levelUnit l E X P n)
        (CoefficientCone.coneToTensor_zero l E X data hdata P n))
  have hc : QuasiIso c := by
    have hh := CoefficientCone.coneToTensor_quasiIso l E X data hdata P hP n
    change QuasiIso ((eqToIso (data.hobj n P)).hom ≫ c) at hh
    exact (quasiIso_iff_comp_left (eqToIso (data.hobj n P)).hom c).mp hh
  have hz' (p j k : ℤ) (h : p + j = k) (hj : j ≠ 0) :
      HomologicalComplex.ιMapBifunctor (complex l E X P)
          ((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n))
          (curriedTensor _) (.up ℤ) p j k h ≫ v.f k = 0 := by
    subst k
    exact hz p j hj
  have heq : G.map c = e.hom ≫ v := by
    apply HomologicalComplex.hom_ext
    intro q
    apply map_cone_hom_ext F s q
    · have hc₁ : (CochainComplex.mappingCone.inl s).v (q + 1) q (by omega) ≫ c.f q = 0 := by
        simp [c, CochainComplex.mappingCone.descShortComplex]
      change F.map ((CochainComplex.mappingCone.inl s).v (q + 1) q (by omega)) ≫
          F.map (c.f q) =
        F.map ((CochainComplex.mappingCone.inl s).v (q + 1) q (by omega)) ≫
          (e.hom.f q ≫ v.f q)
      rw [← F.map_comp, hc₁, F.map_zero, ← Category.assoc]
      obtain ⟨z, hzq⟩ := he₁ q
      rw [hzq, Category.assoc, hz' (q + 1) (-1) q (by omega) (by omega), comp_zero]
    · have hc₀ : (CochainComplex.mappingCone.inr s).f q ≫ c.f q =
          (AdicCompletion.levelUnit l E X P n).f q := by
        simp [c, CochainComplex.mappingCone.descShortComplex]
      have huq := congrArg (fun f ↦ f.f q) hu
      change (ringedKoszulTensorUnitComponent (ring l E X) 1 (fun _ ↦ a)
          (complex l E X P) (op n)).f q ≫ v.f q =
        F.map ((AdicCompletion.levelUnit l E X P n).f q) at huq
      change F.map ((CochainComplex.mappingCone.inr s).f q) ≫ F.map (c.f q) =
        F.map ((CochainComplex.mappingCone.inr s).f q) ≫ (e.hom.f q ≫ v.f q)
      rw [← F.map_comp, hc₀, ← Category.assoc, he₀, huq]
  have hGc : QuasiIso (G.map c) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology c F
  rw [heq] at hGc
  exact (quasiIso_iff_comp_left e.hom v).mp hGc

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
