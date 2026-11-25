/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverDescent
public import WeilConjectures.WeilSheaf.BoundaryStalkFrobenius
public import WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# Boundary stalks of direct images through the generic specialization

Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of `k₀`-schemes, `F` a Weil sheaf on `U₀`,
`h : Spec A ⟶ C̄` a pro-étale neighbourhood of a geometric point with a point `ε` of `Spec A`
over a point `η` of `Ū`. The *generic specialization*
`Γ(Spec A, h^* j_* F) ⟶ Γ(Spec Ω, (η ≫ j̄)^* j_* F) ⟶ Γ(Spec Ω, η^* F)`
(`AlgebraicGeometry.WeilSheaf.genericSpecialization`) is the restriction along `ε` followed by the
counit `j̄^* j̄_* F ⟶ F`. It intertwines the transports along lifts of the Frobenius
(`AlgebraicGeometry.WeilSheaf.genericSpecialization_frobenius`), and on germs it is the
restriction of sections of `F` from `Spec A ×_C̄ Ū` to `Spec Ω`
(`AlgebraicGeometry.WeilSheaf.germ_diagLift_comp_genericSpecialization`).

For a strictly henselian neighbourhood of the geometric point of a closed point `x`, whose
punctured part is the spectrum of a field `K'`, and a Galois extension `Ω / K'`, this gives an
injective linear map from the stalk `(j_* F)_x̄` to `Γ(Spec Ω, η^* F)` with image the
`Gal(Ω / K')`-invariants, intertwining the Frobenius of the stalk with the transport along a lift
of the Frobenius (`AlgebraicGeometry.WeilSheaf.exists_stalk_directImage_linearMap_invariants`).
This is the stalk side of blueprint `lemma-boundary-stalk--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The transport along the trivial square `𝟙 ≫ (t ≫ g) = t ≫ g` and `θ : g^* P ⟶ Q` is
`Γ(S, (t ≫ g)^* P) ≅ Γ(S, t^* g^* P) ⟶ Γ(S, t^* Q)`. -/
lemma globalSectionsTransport_refl_eq {S Y Z : Scheme.{u}} (t : S ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (ProEt.topology Z) A) {Q : Sheaf (ProEt.topology Y) A} (θ : (g)^*[A].obj P ⟶ Q) :
    globalSectionsTransport A (τ := (Iso.refl S).hom) (Category.id_comp (t ≫ g)) θ =
      (Sheaf.Γ _ A).map ((upperStarComp A t g).hom.app P ≫ (t)^*[A].map θ) := by
  change globalSectionsTransport A (τ := 𝟙 S) (Category.id_comp (t ≫ g)) θ = _
  rw [globalSectionsTransport, globalSectionsToUpperStar_id_app, ← Functor.map_comp,
    upperStarCompIso]
  congr 1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← reassoc_of% (upperStarComp_id_left_hom_app A (t ≫ g) P), Iso.inv_hom_id_app_assoc]
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- A lift `t` of `T` through `V ×_Y T` is the lift given by its first component. -/
lemma eq_overLift {Y T : Scheme.{u}} (V : Y.ProEt) {g : T ⟶ Y}
    (t : ProEt.mk (𝟙 T) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    t = overLift V (t.left ≫ pullback.fst V.hom g) (by
      have hw : t.left ≫ pullback.snd V.hom g = 𝟙 T := MorphismProperty.Over.w t
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
      exact Category.id_comp g) := by
  have hw : t.left ≫ pullback.snd V.hom g = 𝟙 T := MorphismProperty.Over.w t
  refine MorphismProperty.Over.Hom.ext ?_
  apply pullback.hom_ext
  · simp [overLift]
  · simp [overLift, hw]
    try rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open ProEtale Scheme

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

section StalkFrobenius

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X)

/-- The Frobenius of the stalk at `s` relative to `𝔽_{qᵐ}`, on elements, is the transport of
global sections along the iterated Weil structure. -/
lemma stalkAt_frobenius_apply
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (v) :
    (G.stalkAt s m hs).frobenius v = ((WeilCoefficients.toModuleCat l).map
      (globalSectionsTransport _ hs.symm (G.frobeniusPowStr m))).hom v :=
  LinearMap.congr_fun (frobeniusEnd_stalkAt G s m hs) v

/-- The geometric stalk at a closed point is the stalk at the attached geometric point. (Stated
through `congrArg`: the kernel checks the direct definitional unfolding slowly.) -/
lemma stalk_frobenius_apply_eq (x : X.finitePoints) (v : (G.stalk x).carrier) :
    (G.stalk x).frobenius v = (G.stalkAt _ _
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
        (X ↘ Spec (CommRingCat.of k₀)) x)).frobenius v :=
  congrArg (fun f : (G.stalk x).carrier ≃ₗ[PadicAlgCl l] (G.stalk x).carrier ↦ f v) rfl

/-- The Frobenius of the geometric stalk at a closed point `x`, `m = deg x`, is the transport of
global sections along `σᵐ ≫ x̄ = x̄ ≫ Frᵐ` and the iterated Weil structure. -/
lemma stalk_frobenius_apply (x : X.finitePoints) (v) :
    (G.stalk x).frobenius v = ((WeilCoefficients.toModuleCat l).map
      (globalSectionsTransport _
        (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
          (X ↘ Spec (CommRingCat.of k₀)) x).symm (G.frobeniusPowStr _))).hom v :=
  (stalk_frobenius_apply_eq G x v).trans (stalkAt_frobenius_apply G _ _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x) v)

/-- A linear map `S` out of the global sections at the geometric point of a closed point `x`
intertwining the transport along the iterated Weil structure with `Ψ` intertwines the Frobenius
of the stalk with `Ψ`. (Stated for an arbitrary `G`: the kernel checks the identification of the
stalk with the global sections slowly for explicit `G`.) -/
lemma stalk_frobenius_intertwine {W : Type*} [AddCommGroup W] [Module (PadicAlgCl l) W]
    (x : X.finitePoints)
    (S : (WeilCoefficients.toModuleCat l).obj ((Sheaf.Γ _ _).obj
      (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)^*[_].obj
        G.obj.carrier.X)) →ₗ[PadicAlgCl l] W) (Ψ : W →ₗ[PadicAlgCl l] W)
    (hS : ∀ w, S (((WeilCoefficients.toModuleCat l).map
        (globalSectionsTransport _
          (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
            (X ↘ Spec (CommRingCat.of k₀)) x).symm (G.frobeniusPowStr _))).hom w) = Ψ (S w))
    (v : (G.stalk x).carrier) :
    (S : (G.stalk x).carrier →ₗ[PadicAlgCl l] W) ((G.stalk x).frobenius v) =
      Ψ ((S : (G.stalk x).carrier →ₗ[PadicAlgCl l] W) v) :=
  (congrArg S (stalk_frobenius_apply G x v)).trans (hS v)

/-- A morphism `Φ` out of the global sections at the geometric point of a closed point `x`
intertwining the transport along the iterated Weil structure with `Ψ` intertwines the Frobenius
of the stalk with `Ψ`. -/
lemma stalk_frobenius_intertwine_of_comp_eq {Q : WeilCoefficients.{u} l}
    (x : X.finitePoints)
    (Φ : (Sheaf.Γ _ _).obj
      (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)^*[_].obj
        G.obj.carrier.X) ⟶ Q) (Ψ : Q ⟶ Q)
    (hΦ : globalSectionsTransport _
          (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
            (X ↘ Spec (CommRingCat.of k₀)) x).symm (G.frobeniusPowStr _) ≫ Φ = Φ ≫ Ψ)
    (v : (G.stalk x).carrier) :
    (((WeilCoefficients.toModuleCat l).map Φ).hom : (G.stalk x).carrier →ₗ[PadicAlgCl l] _)
        ((G.stalk x).frobenius v) =
      ((WeilCoefficients.toModuleCat l).map Ψ).hom
        ((((WeilCoefficients.toModuleCat l).map Φ).hom :
          (G.stalk x).carrier →ₗ[PadicAlgCl l] _) v) := by
  refine stalk_frobenius_intertwine G x _ _ (fun w ↦ ?_) v
  have := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom w) hΦ
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at this
  exact this

end StalkFrobenius

section Generic

variable {F} {A : Type u} [CommRing A]
  (h : Spec (.of A) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  {Ω : Type u} [Field Ω] (η : Spec (.of Ω) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (ε : Spec (.of Ω) ⟶ Spec (.of A)) (hε : ε ≫ h = η ≫ j̄)
  (P : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (WeilCoefficients.{u} l)) (θ : (j̄)^*[WeilCoefficients.{u} l].obj P ⟶ F.obj.carrier.X)

/-- **The generic specialization** `Γ(Spec A, h^* P) ⟶ Γ(Spec Ω, η^* F)` along `θ : j̄^* P ⟶ F`:
the restriction along a point `ε : Spec Ω ⟶ Spec A` over `η ≫ j̄`, followed by `θ`. For
`P = j̄_* F` and `θ` the counit `j̄^* j̄_* F ⟶ F` this is the specialization of sections of `j_* F`
over a neighbourhood to the generic point. -/
noncomputable def genericSpecialization :
    (Sheaf.Γ _ _).obj ((h)^*[WeilCoefficients.{u} l].obj P) ⟶
      (Sheaf.Γ _ _).obj ((η)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X) :=
  (ProEtale.resOver _ ε hε).app _ ≫
    ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (η ≫ j̄)) θ

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j] in
/-- **The generic specialization intertwines the Frobenius lifts.** For `θ` compatible with the
Weil structures, a lift `α` of `Frᵐ` to `Spec A` and `a` of `Frᵐ` to `Spec Ω` with
`a ≫ ε = ε ≫ α`, the generic specialization intertwines the transports along `α` and `a` and the
iterated Weil structures. -/
theorem genericSpecialization_frobenius (G : WeilSheaf k₀ l X)
    (θ : (j̄)^*[WeilCoefficients.{u} l].obj G.obj.carrier.X ⟶ F.obj.carrier.X)
    (hθ : (ProEtale.upperStarComp _
      (U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (j̄)).hom.app G.obj.carrier.X ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map θ ≫
          F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          j (comp_over j (Spec (CommRingCat.of k₀)))).symm).hom.app G.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (j̄)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            G.obj.carrier.X ≫
        (j̄)^*[_].map G.frobeniusStr ≫ θ)
    (m : ℕ) (hm : 1 ≤ m) (α : Spec (.of A) ⟶ Spec (.of A))
    (hα : α ≫ h = h ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ η = η ≫ ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (haε : a ≫ ε = ε ≫ α) :
    ProEtale.globalSectionsTransport _ hα (G.frobeniusPowStr m) ≫
        genericSpecialization j h η ε hε G.obj.carrier.X θ =
      genericSpecialization j h η ε hε G.obj.carrier.X θ ≫
        ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr m) := by
  have haC : a ≫ (η ≫ j̄) =
      (η ≫ j̄) ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom := by
    rw [← Category.assoc, ha, Category.assoc, Category.assoc,
      ← Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow]
  rw [genericSpecialization, ← Category.assoc,
    ProEtale.globalSectionsTransport_comp_resOver hα haC ε hε haε, Category.assoc,
    globalSectionsTransport_frobeniusPowStr_comp_upperStar hθ m hm ha haC, Category.assoc]

end Generic

section Neighbourhood

variable {A : Type u} [CommRing A]
  (h : Spec (.of A) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale h]
  {K' Ω : Type u} [Field K'] [Field Ω] [Algebra K' Ω] [Algebra.IsSeparable K' Ω]
  (k : Spec (.of K') ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale k]
  (e : Scheme.ProEt.mk k ≅
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h))

variable (Ω) in
/-- The generic point `Spec Ω ⟶ Spec K' ≅ Spec A ×_C̄ Ū ⟶ Spec A` of the neighbourhood. -/
noncomputable abbrev nbhdGenericPoint : Spec (.of Ω) ⟶ Spec (.of A) :=
  specFieldMap K' Ω ≫ e.hom.left ≫ pullback.fst h (j̄)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] [Finite k₀]
  [IsOpenImmersion j] [Algebra.IsSeparable K' Ω] in
lemma nbhdGenericPoint_comp :
    nbhdGenericPoint j h Ω k e ≫ h = (specFieldMap K' Ω ≫ k) ≫ j̄ := by
  have hw : e.hom.left ≫ pullback.snd h (j̄) = k := MorphismProperty.Over.w e.hom
  rw [nbhdGenericPoint, Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc e.hom.left, hw, Category.assoc]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] [Finite k₀]
  [IsOpenImmersion j] [Algebra.IsSeparable K' Ω] in
/-- The lift of `Spec Ω` through the iterated base change, given by the generic point. -/
lemma overLift_nbhdGenericPoint_comp_pullbackComp :
    overLift (Scheme.ProEt.mk h) (nbhdGenericPoint j h Ω k e) (nbhdGenericPoint_comp j h k e) ≫
      (MorphismProperty.Over.pullbackComp (specFieldMap K' Ω ≫ k) (j̄)).hom.app
        (Scheme.ProEt.mk h) =
      overLift ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h))
        (specFieldMap K' Ω ≫ e.hom.left)
        (by
          rw [Category.assoc]
          exact congrArg (specFieldMap K' Ω ≫ ·) (MorphismProperty.Over.w e.hom)) := by
  refine MorphismProperty.Over.Hom.ext ?_
  erw [MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [overLift, MorphismProperty.Over.homMk_hom, Over.homMk_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullback.map_id, Category.id_comp, pullbackLeftPullbackSndIso_inv_fst, pullback.lift_fst,
        pullback.lift_fst_assoc]
      simp only [nbhdGenericPoint, Category.assoc]
      rfl
    · simp only [overLift, MorphismProperty.Over.homMk_hom, Over.homMk_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullback.map_id, Category.id_comp, pullbackLeftPullbackSndIso_inv_fst_snd,
        pullback.lift_snd_assoc, pullback.lift_fst_assoc]
      simp only [Category.assoc]
      exact congrArg (specFieldMap K' Ω ≫ ·) (MorphismProperty.Over.w e.hom).symm
  · simp only [overLift, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
    erw [pullback.map_id, Category.id_comp, pullbackLeftPullbackSndIso_inv_snd_snd,
      pullback.lift_snd, pullback.lift_snd]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] [IsOpenImmersion j] in
/-- **The generic specialization on germs.** The germ along the diagonal of the neighbourhood
followed by the generic specialization is the restriction of sections of `F` from
`Spec A ×_C̄ Ū = Spec K'` to `Spec Ω`, followed by the germ along the diagonal of `Spec Ω`. -/
lemma germ_diagLift_comp_genericSpecialization :
    germ _ (Scheme.ProEt.mk h).hom ((j̄)_*[_].obj F.obj.carrier.X)
        (diagLift (Scheme.ProEt.mk h)) ≫
      genericSpecialization j h (specFieldMap K' Ω ≫ k) (nbhdGenericPoint j h Ω k e)
        (nbhdGenericPoint_comp j h k e) ((j̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X)
        ((ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X) =
      F.obj.carrier.X.obj.map e.hom.op ≫ F.obj.carrier.X.obj.map (fieldExtHom Ω k).op ≫
        germ _ (fieldExtObj Ω k).hom F.obj.carrier.X (diagLift (fieldExtObj Ω k)) := by
  have hℓ : (specFieldMap K' Ω ≫ e.hom.left) ≫
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h)).hom =
      specFieldMap K' Ω ≫ k := by
    rw [Category.assoc]
    exact congrArg (specFieldMap K' Ω ≫ ·) (MorphismProperty.Over.w e.hom)
  -- the left side, as a germ of `F` along `η`
  have e₁ := germ_overLift (WeilCoefficients.{u} l) ((j̄)_*[_].obj F.obj.carrier.X)
    (Scheme.ProEt.mk h) (nbhdGenericPoint j h Ω k e) (nbhdGenericPoint_comp j h k e)
  have e₂ := germ_comp_lowerStar (WeilCoefficients.{u} l) (specFieldMap K' Ω ≫ k) (j̄)
    F.obj.carrier.X _ _ (overLift_nbhdGenericPoint_comp_pullbackComp j h k e)
  have e₃ := germ_overLift (WeilCoefficients.{u} l) F.obj.carrier.X
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h))
    (specFieldMap K' Ω ≫ e.hom.left) hℓ
  -- the right side
  have e₄ := map_comp_germ_diagLift (WeilCoefficients.{u} l) F.obj.carrier.X
    (fieldExtHom Ω k ≫ e.hom)
  rw [genericSpecialization, ProEtale.globalSectionsTransport_refl_eq, ← Category.assoc, ← e₁,
    e₂, e₃, ← Category.assoc, ← Functor.map_comp, ← op_comp, e₄]
  rfl

section Specialization

variable [IsStrictlyHenselianLocalRing A] [Normal K' Ω] (x : X.finitePoints)
  (t : Scheme.ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)).obj
      (Scheme.ProEt.mk h))

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- **The boundary stalk of `j_* F` as Galois invariants, Frobenius-equivariantly.** Let
`h : Spec A ⟶ C̄` be a weakly étale neighbourhood of the geometric point `x̄` of a closed point `x`
through the closed point of the strictly henselian `Spec A`, whose punctured part
`Spec A ×_C̄ Ū` is `k : Spec K' ⟶ Ū`, and `Ω / K'` a Galois extension. Given lifts `α` of the
Frobenius `Frᵐ`, `m = deg x`, to `Spec A` and `a` to `Spec Ω`, compatible with the lift of `x̄`
and with the generic point `Spec Ω ⟶ Spec A`, there is an injective linear map
`(j_* F)_x̄ ⟶ Γ(Spec Ω, η^* F)`, `η : Spec Ω ⟶ Spec K' ⟶ Ū`, with image the
`Gal(Ω / K')`-invariants, intertwining the Frobenius of the stalk with the transport along
`a ≫ η = η ≫ Frᵐ` and the Weil structure of `F`.
(blueprint: `lemma-boundary-stalk--1`) -/
theorem exists_stalk_directImage_linearMap_invariants (hF : F.IsLisse)
    (ht : (t.left ≫ pullback.fst h _) (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      IsLocalRing.closedPoint A)
    (α : Spec (.of A) ⟶ Spec (.of A))
    (hα : α ≫ h = h ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom)
    (hcα : (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom ≫
      (t.left ≫ pullback.fst h _) = (t.left ≫ pullback.fst h _) ≫ α)
    (η : Spec (.of Ω) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hη : specFieldMap K' Ω ≫ k = η) (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ η = η ≫
      ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom)
    (haε : a ≫ nbhdGenericPoint j h Ω k e = nbhdGenericPoint j h Ω k e ≫ α) :
    ∃ Sp : (((lowerStar j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        (WeilCoefficients.toModuleCat l).obj
          ((Sheaf.Γ _ _).obj ((η)^*[_].obj F.obj.carrier.X)),
      Function.Injective Sp ∧
      (∀ u, u ∈ LinearMap.range Sp ↔ ∀ σ : Ω ≃ₐ[K'] Ω,
        ((WeilCoefficients.toModuleCat l).map ((resOver _ _
          (show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ η = η by
              rw [← hη, ← Category.assoc, specMap_algEquiv_comp_specFieldMap])).app
                F.obj.carrier.X)).hom u = u) ∧
      ∀ v, Sp ((((lowerStar j).obj F).stalk x).frobenius v) =
        ((WeilCoefficients.toModuleCat l).map
          (globalSectionsTransport _ ha (F.frobeniusPowStr _))).hom (Sp v) := by
  subst hη
  set P := ((lowerStar j).obj F).obj.carrier.X
  have hc : (t.left ≫ pullback.fst h
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)) ≫ h =
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x := by
    have hw : t.left ≫ pullback.snd h
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) = 𝟙 _ :=
      MorphismProperty.Over.w t
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact Category.id_comp _
  set DA := germ (WeilCoefficients.{u} l) (Scheme.ProEt.mk h).hom P
    (diagLift (Scheme.ProEt.mk h))
  set rc := (resOver (WeilCoefficients.{u} l) _ hc).app P
  have hgD : germ (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) P t = DA ≫ rc := by
    conv_lhs => rw [eq_overLift _ t]
    exact germ_overLift _ P (Scheme.ProEt.mk h) _ hc
  have hg : Function.Bijective (germ (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) P t) :=
    bijective_germ_of_weaklyEtale_of_isStrictlyHenselianLocalRing _ h P t ht
  set g := germ (WeilCoefficients.{u} l)
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) P t
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective g).2 hg
  have : IsIso rc := by
    have : rc = inv DA ≫ g := by rw [hgD, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have hinv : inv rc = inv g ≫ DA := by
    apply IsIso.inv_eq_of_inv_hom_id
    rw [Category.assoc, ← hgD, IsIso.inv_hom_id]
  set GS := genericSpecialization j h (specFieldMap K' Ω ≫ k) (nbhdGenericPoint j h Ω k e)
    (nbhdGenericPoint_comp j h k e) P
    ((ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X)
  set DΩ := germ (WeilCoefficients.{u} l) (fieldExtObj Ω k).hom F.obj.carrier.X
    (diagLift (fieldExtObj Ω k))
  have hDΩ : Function.Bijective DΩ := ConcreteCategory.bijective_of_isIso DΩ
  -- the specialization on sections over the neighbourhood
  set ρ := F.obj.carrier.X.obj.map e.hom.op ≫ F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
  have hρi : Function.Injective ρ := by
    have he : Function.Injective (F.obj.carrier.X.obj.map e.hom.op) :=
      (ConcreteCategory.bijective_of_isIso (F.obj.carrier.X.obj.map e.hom.op)).1
    have hinj : Function.Injective (F.obj.carrier.X.obj.map (fieldExtHom Ω k).op) :=
      hF.injective_map_fieldExtHom k
    have := hinj.comp he
    intro p q hpq
    apply this
    simp only [Function.comp_apply, ← ConcreteCategory.comp_apply]
    exact hpq
  have key := germ_diagLift_comp_genericSpecialization (Ω := Ω) j F h k e
  set Φ := inv rc ≫ GS
  have hΦ : Φ = inv g ≫ ρ ≫ DΩ := by
    simp only [Φ, hinv, Category.assoc]
    erw [key]
    rfl
  have hSp (v) : ((WeilCoefficients.toModuleCat l).map Φ).hom v = DΩ (ρ ((inv g) v)) := by
    change Φ v = _
    rw [hΦ]
    rfl
  -- the Galois action on `Γ(Spec Ω, η^* F)` and on sections over `Spec Ω`
  have hσ (σ : Ω ≃ₐ[K'] Ω) (q) :
      ((WeilCoefficients.toModuleCat l).map ((resOver _ _
        (show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (specFieldMap K' Ω ≫ k) =
          specFieldMap K' Ω ≫ k by
            rw [← Category.assoc, specMap_algEquiv_comp_specFieldMap])).app
              F.obj.carrier.X)).hom (DΩ q) =
        DΩ (F.obj.carrier.X.obj.map (fieldExtAut k σ).op q) :=
    (ConcreteCategory.congr_hom
      (map_comp_germ_diagLift (WeilCoefficients.{u} l) F.obj.carrier.X (fieldExtAut k σ)) q).symm
  have hinvg (w) : (inv g) (g w) = w := by
    rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
  refine ⟨((WeilCoefficients.toModuleCat l).map Φ).hom,
    fun v w hvw ↦ ?_, fun u ↦ ⟨?_, fun hu ↦ ?_⟩, fun v ↦ ?_⟩
  · have h' : DΩ (ρ ((inv g) v)) = DΩ (ρ ((inv g) w)) := (hSp v).symm.trans (hvw.trans (hSp w))
    exact (ConcreteCategory.bijective_of_isIso (inv g)).1 (hρi (hDΩ.1 h'))
  · rintro ⟨v, rfl⟩ σ
    refine (congrArg _ (hSp v)).trans ((hσ σ _).trans ((congrArg DΩ ?_).trans (hSp v).symm))
    exact map_fieldExtAut_map_fieldExtHom k σ _
  · obtain ⟨q, rfl⟩ := hDΩ.2 u
    have hq (σ : Ω ≃ₐ[K'] Ω) : F.obj.carrier.X.obj.map (fieldExtAut k σ).op q = q :=
      hDΩ.1 ((hσ σ q).symm.trans (hu σ))
    obtain ⟨s, hs⟩ := hF.exists_map_fieldExtHom_eq k q hq
    refine ⟨g (F.obj.carrier.X.obj.map e.inv.op s), (hSp _).trans ?_⟩
    rw [hinvg]
    have hee : F.obj.carrier.X.obj.map e.hom.op (F.obj.carrier.X.obj.map e.inv.op s) = s := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    change DΩ (F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
      (F.obj.carrier.X.obj.map e.hom.op (F.obj.carrier.X.obj.map e.inv.op s))) = DΩ q
    rw [hee, hs]
  · have hpos : 1 ≤ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 :=
      Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ x.2)
    have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x
    have h₁ := globalSectionsTransport_comp_resOver hα hs.symm _ hc hcα P
      (((lowerStar j).obj F).frobeniusPowStr _)
    have h₂ : globalSectionsTransport _ hs.symm (((lowerStar j).obj F).frobeniusPowStr _) ≫
        inv rc = inv rc ≫ globalSectionsTransport _ hα
          (((lowerStar j).obj F).frobeniusPowStr _) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, ← h₁, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    have h₃ := genericSpecialization_frobenius j h (specFieldMap K' Ω ≫ k)
      (nbhdGenericPoint j h Ω k e) (nbhdGenericPoint_comp j h k e) ((lowerStar j).obj F) _
      (counit_frobeniusStr_compatible j F) _ hpos α hα a ha haε
    have hm : globalSectionsTransport _ hs.symm (((lowerStar j).obj F).frobeniusPowStr _) ≫ Φ =
        Φ ≫ globalSectionsTransport _ ha (F.frobeniusPowStr _) := by
      simp only [Φ]
      rw [reassoc_of% h₂, h₃, Category.assoc]
    exact stalk_frobenius_intertwine_of_comp_eq ((lowerStar j).obj F) x _ _ hm v

end Specialization

end Neighbourhood

end AlgebraicGeometry.WeilSheaf
