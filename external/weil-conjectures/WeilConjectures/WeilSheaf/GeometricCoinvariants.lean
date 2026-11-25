/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkPairing
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Purity of the geometric coinvariants

Let `F` be a lisse Weil sheaf on a `k₀`-scheme `X` locally of finite type, punctually `ι`-pure of
weight `w`. Its geometric coinvariants `Γ(X̄, F^∨)^∨`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) are `ι`-pure of weight `w`
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`).

Let `β` be an eigenvalue of the Frobenius on the global sections `Γ(X̄, G)` of a Weil sheaf `G`,
with eigenvector `a`. The morphism of sheaves `ℚ̄_ℓ ⟶ G` sending `1` to `a`
(`AlgebraicGeometry.ProEtale.bijective_globalSectionOfModHom`) is a morphism of Weil sheaves
`u : ℚ̄_ℓ(β) ⟶ G` out of the constant Weil twist of `ℚ̄_ℓ` by `β`
(`AlgebraicGeometry.WeilSheaf.homOfGlobalSection`). Its image is nonzero, so it has a nonzero
stalk at some closed point `x`, a quotient of the stalk of `ℚ̄_ℓ(β)`, on which the local
Frobenius acts by `β^{deg x}`. Hence `β^{deg x}` is an eigenvalue of the local Frobenius of `G`
at `x` (`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`).

For `G = F^∨`, whose stalks are the duals of those of `F`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_dual`), this shows that every eigenvalue of
the Frobenius on `Γ(X̄, F^∨)` has weight `-w`, so that its dual has weight `w`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace FrobeniusModule

variable {K : Type*} [Field K]

lemma frobeniusEnd_apply (M : FrobeniusModule K) (x : M.carrier) :
    M.frobeniusEnd x = M.frobenius x :=
  rfl

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section GlobalSections

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The Frobenius of the global sections of a Weil sheaf: the inverse of
`Γ(X̄, Fr^* G) ≅ Γ(X̄, G)` followed by the global sections of the Weil structure. -/
lemma globalSections_frobenius_apply (G : WeilSheaf k₀ l X) (a : G.globalSections.carrier) :
    G.globalSections.frobenius a = ((Sheaf.Γ _ _).map G.obj.str.hom.hom).hom
      (((globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app
          G.obj.carrier.X).hom a) :=
  rfl

end GlobalSections

/-- The Weil structure of the constant Weil sheaf `ℚ̄_ℓ` fixes the global section `1`. -/
lemma adicConstant_globalSections_str_one :
    ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.hom.hom).hom
      (((globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app
          (adicConstant k₀ l X).obj.carrier.X).hom
        (oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) =
      oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber := by
  have hε := NatTrans.IsMonoidal.unit (τ := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).hom)
  have key : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫
      (Sheaf.Γ _ _).map (MonObj.one (X := adicConstantSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ≫
      (globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app _ ≫
      (Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.hom.hom =
      ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫
        (Sheaf.Γ _ _).map (MonObj.one (X := adicConstantSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) := by
    have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality
        (MonObj.one (X := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    have hε' : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app (𝟙_ _) =
        ε (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_] ⋙
          Sheaf.Γ _ (WeilCoefficients.{u} l)) := by
      rw [← hε, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    erw [reassoc_of% n, reassoc_of% hε']
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp]
    have hu := adicConstant_unit_str (k₀ := k₀) (l := l) (X := X)
    rw [Category.assoc] at *
    exact congrArg (fun m ↦ ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map m) hu
  exact congrArg (fun m ↦ m.hom (1 : ULift.{u + 1} (PadicAlgCl l))) key

section Hom

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The morphism of sheaves of modules `ℚ̄_ℓ ⟶ G` sending `1` to a global section `a` of a Weil
sheaf `G`. -/
noncomputable def modHomOfGlobalSection (G : WeilSheaf k₀ l X) (a : G.globalSections.carrier) :
    AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶ G.obj.carrier :=
  Function.surjInv (bijective_globalSectionOfModHom G.obj.carrier).2 a

lemma globalSectionOfModHom_modHomOfGlobalSection (G : WeilSheaf k₀ l X)
    (a : G.globalSections.carrier) :
    globalSectionOfModHom (modHomOfGlobalSection G a) = a :=
  Function.surjInv_eq _ a

/-- The morphism `ℚ̄_ℓ ⟶ G` of a Frobenius eigenvector `a` with eigenvalue `β` intertwines the
Weil structure of `G` with the Weil structure of `ℚ̄_ℓ` twisted by `β`. -/
theorem modHomOfGlobalSection_comm (G : WeilSheaf k₀ l X) (β : (PadicAlgCl l)ˣ)
    (a : G.globalSections.carrier) (ha : G.globalSections.frobenius a = (β : PadicAlgCl l) • a) :
    (frobeniusPullback k₀ l X).map (modHomOfGlobalSection G a) ≫ G.obj.str.hom =
      ((adicConstant k₀ l X).constantTwist β).obj.str.hom ≫ modHomOfGlobalSection G a := by
  set v := modHomOfGlobalSection G a with hv_def
  have hv : ((Sheaf.Γ _ _).map v.hom).hom
      (oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) = a := by
    rw [← globalSectionOfModHom_eq]
    exact globalSectionOfModHom_modHomOfGlobalSection G a
  let gs := globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
  let one := oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have e₁ : ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.inv.hom).hom one =
      (gs.inv.app _).hom one := by
    have h := congrArg ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.inv.hom).hom
      (adicConstant_globalSections_str_one (k₀ := k₀) (l := l) (X := X))
    rw [← h, ← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', Iso.hom_inv_id,
      Mod.id_hom', CategoryTheory.Functor.map_id]
    rfl
  have e₂ : G.globalSections.frobenius a = ((Sheaf.Γ _ _).map G.obj.str.hom.hom).hom
      (((Sheaf.Γ _ _).map ((frobeniusPullback k₀ l X).map v).hom).hom
        (gs.inv.app _ |>.hom one)) := by
    rw [globalSections_frobenius_apply, ← hv,
      ← ModuleCat.comp_apply (f := (Sheaf.Γ _ _).map v.hom)]
    erw [gs.inv.naturality v.hom]
    rfl
  rw [← cancel_epi (adicConstant k₀ l X).obj.str.inv]
  refine (bijective_globalSectionOfModHom G.obj.carrier).1 ?_
  rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq]
  have e₃ (y) : ((Sheaf.Γ _ _).map
      ((adicConstant k₀ l X).constantTwist β).obj.str.hom.hom).hom y =
      (ULift.up (β : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) •
        ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.hom.hom).hom y := by
    have hs : ((adicConstant k₀ l X).constantTwist β).obj.str.hom.hom =
        (adicConstant k₀ l X).obj.str.hom.hom ≫
          ((ULift.up (β : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _) := by
      simp only [constantTwist, Endofunctor.IsoAlgebra.mk_str, Iso.trans_hom, Mod.comp_hom',
        WeilCoefficients.smulIso, AdicSheaf.smul_hom]
    rw [hs, Functor.map_comp, Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  simp only [Mod.comp_hom', Functor.map_comp, ModuleCat.comp_apply]
  erw [e₁, ← e₂, e₃]
  erw [adicConstant_globalSections_str_one (k₀ := k₀) (l := l) (X := X)]
  rw [map_smul]
  erw [hv, ha]
  rfl

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The stalk at a closed point is the stalk at the chosen geometric point over it. -/
lemma stalk_eq_stalkAt (F : WeilSheaf k₀ l X) (x : X.finitePoints) :
    F.stalk x = F.stalkAt _ _
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
        (X ↘ Spec (CommRingCat.of k₀)) x) :=
  rfl

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The local Frobenius of the constant Weil sheaf twisted by `b` at a closed point `x` is the
multiplication by `b ^ deg x`. -/
lemma constantTwist_adicConstant_stalk_frobenius (b : (PadicAlgCl l)ˣ) (x : X.finitePoints)
    (c : (((adicConstant k₀ l X).constantTwist b).stalk x).carrier) :
    (((adicConstant k₀ l X).constantTwist b).stalk x).frobenius c =
      ((b : PadicAlgCl l) ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) • c := by
  obtain ⟨e⟩ := nonempty_equiv_stalk_constantTwist (adicConstant k₀ l X) b x
  apply e.toLinearEquiv.injective
  rw [e.map_frobenius, map_smul]
  have h₁ := FrobeniusModule.frobeniusEnd_rescale_apply
    (M := (adicConstant k₀ l X).stalk x) (pow_ne_zero
      ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) b.ne_zero) (e.toLinearEquiv c)
  rw [FrobeniusModule.frobeniusEnd_apply, FrobeniusModule.frobeniusEnd_apply] at h₁
  have h₂ : ((adicConstant k₀ l X).stalk x).frobenius = LinearEquiv.refl _ _ := by
    rw [stalk_eq_stalkAt]
    exact adicConstant_stalkAt_frobenius _ _ _
  exact h₁.trans (congrArg (_ • ·) (LinearEquiv.congr_fun h₂ _))

/-- The morphism of Weil sheaves `ℚ̄_ℓ(β) ⟶ G` out of the constant Weil sheaf twisted by `β`
sending `1` to a Frobenius eigenvector `a` with eigenvalue `β` of the global sections of `G`. -/
noncomputable def homOfGlobalSection (G : WeilSheaf k₀ l X) (β : (PadicAlgCl l)ˣ)
    (a : G.globalSections.carrier) (ha : G.globalSections.frobenius a = (β : PadicAlgCl l) • a) :
    (adicConstant k₀ l X).constantTwist β ⟶ G :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨modHomOfGlobalSection G a, modHomOfGlobalSection_comm G β a ha⟩)

lemma homOfGlobalSection_ne_zero (G : WeilSheaf k₀ l X) (β : (PadicAlgCl l)ˣ)
    (a : G.globalSections.carrier) (ha : G.globalSections.frobenius a = (β : PadicAlgCl l) • a)
    (ha₀ : a ≠ 0) : homOfGlobalSection G β a ha ≠ 0 := by
  intro h
  have h₀ : modHomOfGlobalSection G a = 0 := congrArg (fun f ↦ f.hom.hom.f) h
  apply ha₀
  rw [← globalSectionOfModHom_modHomOfGlobalSection G a, h₀, globalSectionOfModHom_eq]
  erw [Mod.zero_hom, Functor.map_zero]
  rfl

/-- **A Frobenius eigenvalue of global sections is, up to a power, a local Frobenius
eigenvalue.** If `β` is an eigenvalue of the Frobenius on the global sections of a Weil sheaf
`G`, then `β ^ deg x` is an eigenvalue of the local Frobenius of `G` at some closed point `x`. -/
theorem exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections (G : WeilSheaf k₀ l X)
    {β : PadicAlgCl l} (hβ : G.globalSections.frobeniusEnd.HasEigenvalue β) :
    ∃ x : X.finitePoints, (G.stalk x).frobeniusEnd.HasEigenvalue
      (β ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) := by
  obtain ⟨a, ha⟩ := hβ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at ha
  obtain ⟨ha, ha₀⟩ := ha
  have hβ₀ : β ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact ha₀ (G.globalSections.frobenius.injective (ha.trans (map_zero _).symm))
  let b := Units.mk0 β hβ₀
  let u := homOfGlobalSection G b a ha
  have hu : u ≠ 0 := homOfGlobalSection_ne_zero G b a ha ha₀
  have hI : ¬ IsZero (image u) := fun hI ↦ hu (by
    rw [← image.fac u, hI.eq_of_src (image.ι u) 0, comp_zero])
  obtain ⟨x, hx⟩ := exists_nontrivial_stalk_of_not_isZero (image u) hI
  obtain ⟨y, hy⟩ := exists_ne (0 : ((image u).stalk x).carrier)
  obtain ⟨c, rfl⟩ := surjective_stalkAtMap _ _ _ (factorThruImage u) y
  have hC : (((adicConstant k₀ l X).constantTwist b).stalk x).frobenius c =
      (β ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) • c :=
    constantTwist_adicConstant_stalk_frobenius b x c
  have hcomp : stalkAtMap _ _ _ u c =
      stalkAtMap _ _ _ (image.ι u) (stalkAtMap _ _ _ (factorThruImage u) c) := by
    rw [stalkAtMap_apply, stalkAtMap_apply, stalkAtMap_apply, ← ModuleCat.comp_apply,
      ← Functor.map_comp, stalkMap, stalkMap, stalkMap, ← Functor.map_comp, image.fac]
  refine ⟨x, Module.End.hasEigenvalue_of_hasEigenvector (x := stalkAtMap _ _ _ u c) ?_⟩
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · rw [FrobeniusModule.frobeniusEnd_apply]
    exact (stalkAtMap_frobenius _ _ _ u c).symm.trans
      ((congrArg (stalkAtMap _ _ _ u) hC).trans (map_smul _ _ _))
  · rw [hcomp]
    exact (map_ne_zero_iff _ (injective_stalkAtMap _ _ _ (image.ι u))).2 hy

/-- *Purity of the geometric coinvariants.* If `F` is a lisse Weil sheaf, punctually `ι`-pure of
weight `w`, then its geometric coinvariants `V_{π₁(X̄)}` with the induced Frobenius are `ι`-pure
of weight `w` (possibly zero). Every eigenvalue `β` of the Frobenius on the global sections of
the dual `F^∨` is, up to the power `deg x`, an eigenvalue of the local Frobenius of `F^∨` at
some closed point `x`
(`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`),
whose stalk is the dual of the stalk of `F`; so `β` has weight `-w`, and its inverse, an
eigenvalue of the coinvariants, has weight `w`.

The blueprint states this for `X` a nonempty smooth geometrically connected curve; here `X` is
only assumed locally of finite type over `k₀`, which is what provides these closed points.
Some such hypothesis is needed: `IsPunctuallyPureOfWeight` only sees the points of
`X.finitePoints`, so for `X = Spec 𝔽_q(t)` it holds for every `w`, while the coinvariants of a
rank-one sheaf need not be pure of every weight.
(blueprint: `lemma-degree-zero-top-cohomology--7`) -/
theorem isPureOfWeightOver_geometricCoinvariants (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l X) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (F.geometricCoinvariants hF).IsPureOfWeightOver k₀ ι w := by
  have hΓ : (F.dual hF).globalSections.IsPureOfWeight ι (Nat.card k₀) (-w) := by
    intro β hβ
    obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections (F.dual hF) hβ
    obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
    have h := (hw x).dual _ (e.hasEigenvalue hx)
    have hm := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
    have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
    rw [map_pow, norm_pow, Scheme.Hom.residueCard, Nat.cast_pow, ← Real.rpow_natCast_mul hq,
      mul_comm, Real.rpow_mul_natCast hq] at h
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hm).1 h
  have h := hΓ.dual
  rw [neg_neg] at h
  exact h

end Hom

end AlgebraicGeometry.WeilSheaf
