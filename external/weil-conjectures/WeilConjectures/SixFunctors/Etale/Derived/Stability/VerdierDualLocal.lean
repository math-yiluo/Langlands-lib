/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteness
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.ConstructibleSheaf.EtaleDescent

/-!
# The Verdier dual of a complex of lisse sheaves on a smooth scheme

Let `O` be an irreducible scheme smooth of pure relative dimension `n` over a field `k`, and `K` a
complex on `O` represented by a bounded complex of flat finite locally constant sheaves in degrees
`[a, b]`. After shrinking `O` to a nonempty open, the Verdier dual `𝔻_O K = RHom(K, ω_O)` has Tor
amplitude in `[-b - 2n, -a - 2n]`.

The proof avoids the dualizability of lisse sheaves: after shrinking `O`, there is a finite étale
surjection `p : V ⟶ O` along which all the terms become constant
(`AlgebraicGeometry.Etale.exists_finite_etale_surjective_isConstant`), hence dualizable, being
constant sheaves of finite projective modules. Along the finite étale `p`, `p^* = Rp^!` commutes
with the internal hom, and `ω_O` is a shifted flat invertible sheaf by smooth duality, so
`p^* 𝔻_O K ≅ RHom(p^* K, p^* ω_O) ≅ (p^* K)^∨ ⊗ᴸ p^* ω_O`; the Tor amplitude then descends along
the surjection `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Trivialising finitely many locally constant sheaves -/

variable {Λ} in
/-- The pullback of a constant sheaf is constant. -/
lemma isConstant_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : F.IsConstant Y.smallEtaleTopology) :
    ((g)^*[ModuleCat.{u + 1} Λ].obj F).IsConstant X.smallEtaleTopology := by
  obtain ⟨⟨M, ⟨e⟩⟩⟩ := hF
  exact Sheaf.isConstant_of_iso _
    ((g)^*[ModuleCat.{u + 1} Λ].mapIso e.symm ≪≫ (upperStarConstantSheafIso _ g).app M)

variable {Λ} in
/-- Finitely many locally constant sheaves on an irreducible scheme become constant after
pullback along a single étale morphism from a nonempty scheme: intersect the images of étale
trivialisations of the individual sheaves, which are nonempty opens of an irreducible space, and
take the fibre product. -/
lemma exists_etale_isConstant_upperStar {O : Scheme.{u}} [IrreducibleSpace O] (n : ℕ)
    (F : Fin n → Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsLocallyConstantSheaf (F i)) :
    ∃ (W : Scheme.{u}) (_ : Nonempty W) (e : W ⟶ O) (_ : _root_.AlgebraicGeometry.Etale e),
      ∀ i, ((e)^*[ModuleCat.{u + 1} Λ].obj (F i)).IsConstant W.smallEtaleTopology := by
  induction n with
  | zero => exact ⟨O, inferInstance, 𝟙 O, inferInstance, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨W, hW, e, he, hc⟩ := ih (fun i ↦ F i.castSucc) (fun i ↦ hF _)
    obtain ⟨⟨𝒰, h𝒰⟩⟩ := (hF (Fin.last n)).nonempty_locallyConstantDatum
    obtain ⟨x⟩ := (inferInstance : Nonempty O)
    let i := 𝒰.idx x
    have hi : _root_.AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    have hci : ((𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj (F (Fin.last n))).IsConstant
        (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar _ _ _).1 (h𝒰 i)
    -- the images of `e` and of `𝒰.f i` meet
    obtain ⟨w⟩ := hW
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨z, ⟨w', hw'⟩, ⟨y', hy'⟩⟩ := nonempty_preirreducible_inter e.isOpenMap.isOpen_range
      (𝒰.f i).isOpenMap.isOpen_range ⟨_, w, rfl⟩ ⟨_, y, rfl⟩
    obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := e) (g := 𝒰.f i) w' y'
      (hw'.trans hy'.symm)
    refine ⟨pullback e (𝒰.f i), ⟨t⟩, pullback.fst e (𝒰.f i) ≫ e, inferInstance, ?_⟩
    intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · have := isConstant_upperStar (pullback.snd e (𝒰.f i)) hci
      exact Sheaf.isConstant_congr (F := (pullback.snd e (𝒰.f i))^*[ModuleCat.{u + 1} Λ].obj
          ((𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj (F (Fin.last n)))) _
        (((Etale.upperStarComp _ (pullback.snd e (𝒰.f i)) (𝒰.f i) _ pullback.condition).app
          (F (Fin.last n))).symm)
    · have := isConstant_upperStar (pullback.fst e (𝒰.f i)) (hc j)
      exact Sheaf.isConstant_congr (F := (pullback.fst e (𝒰.f i))^*[ModuleCat.{u + 1} Λ].obj
          ((e)^*[ModuleCat.{u + 1} Λ].obj (F j.castSucc))) _
        (((Etale.upperStarComp _ (pullback.fst e (𝒰.f i)) e _ rfl).app (F j.castSucc)).symm)

variable {Λ} in
/-- **Generic finite étale trivialisation.** Finitely many locally constant sheaves on an
irreducible locally noetherian scheme `O`, separated over a base, become constant after pullback
along a finite étale surjection onto a nonempty open of `O`: an étale trivialisation from an
affine scheme is finite over a nonempty open
(`AlgebraicGeometry.Scheme.Hom.exists_isFinite_preimage_of_etale`), and a finite étale morphism
onto an irreducible scheme whose image is nonempty is surjective, its image being open and
closed. -/
lemma exists_finite_etale_surjective_isConstant {O S : Scheme.{u}} [IrreducibleSpace O]
    [IsLocallyNoetherian O] (aO : O ⟶ S) [IsSeparated aO] [IsAffine S] (n : ℕ)
    (F : Fin n → Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsLocallyConstantSheaf (F i)) :
    ∃ (O' : O.Opens) (_ : (O' : Set O).Nonempty) (V : Scheme.{u}) (p : V ⟶ O')
      (_ : IsFinite p) (_ : _root_.AlgebraicGeometry.Etale p) (_ : Surjective p),
      ∀ i, ((p ≫ O'.ι)^*[ModuleCat.{u + 1} Λ].obj (F i)).IsConstant V.smallEtaleTopology := by
  obtain ⟨W, ⟨w⟩, e, he, hc⟩ := exists_etale_isConstant_upperStar n F hF
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian e
  -- restrict to a nonempty affine open of `W`
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hwW₀, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  change W.Opens at W₀
  have : IsAffine W₀ := hW₀
  have : Nonempty W₀ := ⟨⟨w, hwW₀⟩⟩
  have : TopologicalSpace.NoetherianSpace W₀ := by
    have : IsLocallyNoetherian W₀ := isLocallyNoetherian_of_isOpenImmersion W₀.ι
    have : IsNoetherian W₀ := {}
    infer_instance
  let e₀ := W₀.ι ≫ e
  have : QuasiCompact e₀ := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsSeparated e₀ := by
    have : IsSeparated (e₀ ≫ aO) := inferInstance
    exact IsSeparated.of_comp e₀ aO
  obtain ⟨O', hO', hpre, hfin⟩ := e₀.exists_isFinite_preimage_of_etale
  let p := e₀ ∣_ O'
  have : _root_.AlgebraicGeometry.Etale p :=
    IsZariskiLocalAtTarget.restrict (P := @_root_.AlgebraicGeometry.Etale) inferInstance O'
  have : IrreducibleSpace O' := by
    obtain ⟨x, hx⟩ := hO'
    exact Subtype.irreducibleSpace ⟨⟨x, hx⟩, IsPreirreducible.open_subset
      (IrreducibleSpace.isIrreducible_univ O).2 O'.isOpen (Set.subset_univ _)⟩
  have hsurj : Surjective p := by
    refine ⟨?_⟩
    have hcl : IsClopen (Set.range p.base) :=
      ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
    obtain ⟨v, hv⟩ := hpre
    rw [← Set.range_eq_univ, hcl.eq_univ ⟨_, ⟨v, hv⟩, rfl⟩]
  refine ⟨O', hO', _, p, hfin, inferInstance, hsurj, fun i ↦ ?_⟩
  have hp : p ≫ O'.ι = (e₀ ⁻¹ᵁ O').ι ≫ W₀.ι ≫ e := morphismRestrict_ι e₀ O'
  have := isConstant_upperStar (e₀ ⁻¹ᵁ O').ι (isConstant_upperStar W₀.ι (hc i))
  exact Sheaf.isConstant_congr (F := ((e₀ ⁻¹ᵁ O').ι)^*[ModuleCat.{u + 1} Λ].obj
      ((W₀.ι)^*[ModuleCat.{u + 1} Λ].obj ((e)^*[ModuleCat.{u + 1} Λ].obj (F i)))) _
    (((e₀ ⁻¹ᵁ O').ι)^*[ModuleCat.{u + 1} Λ].mapIso
      ((Etale.upperStarComp _ W₀.ι e _ rfl).app (F i)).symm ≪≫
      ((Etale.upperStarComp _ (e₀ ⁻¹ᵁ O').ι (W₀.ι ≫ e) _ hp).app (F i)).symm)

/-! ### Dualizability after a finite étale trivialisation -/

section Dualizable

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The constant sheaf of a finite projective `Λ`-module is dualizable, the constant sheaf
functor being monoidal. -/
lemma isDualizable_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    [Module.Projective Λ M] :
    IsDualizable ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  IsDualizable.map _ (ModuleCat.isDualizable_of_projective M)

variable [Finite Λ]

/-- A flat finite sheaf on a nonempty scheme which is constant, with value `M`, has a finite
projective value: the stalk `M` is flat and finitely generated over the noetherian ring `Λ`. -/
lemma projective_and_finite_of_iso_constantSheaf {V : Scheme.{u}} [Nonempty V]
    {G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hG : ObjectProperty.flat G)
    [IsFiniteSheaf G] {M : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ G) :
    Module.Projective Λ M ∧ Module.Finite Λ M := by
  obtain ⟨v⟩ := ‹Nonempty V›
  let s := V.algClosurePoint v
  let Φ := (pointSmallEtale s).ulift.{u + 1}
  let eM : Φ.sheafFiber.obj G ≅ M := Φ.sheafFiber.mapIso e.symm ≪≫ Φ.sheafFiberConstantSheafIso M
  have : Module.Flat Λ M :=
    (ModuleCat.flat_iff_flat M).1 (ObjectProperty.prop_of_iso _ eM (Φ.flat_sheafFiber_obj hG))
  have : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).1
    (((IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := G) _ s).of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G).symm).of_iso
        eM)
  have : IsNoetherianRing Λ := inferInstance
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

/-- **Constant models after a finite étale trivialisation.** Let `O` be an irreducible locally
noetherian scheme, separated over an affine scheme, `P` a bounded complex in degrees `[a, b]` of
flat finite locally constant sheaves of `Λ`-modules on `O`, and `L` a locally constant sheaf.
After shrinking `O` to a nonempty open `O'`, there is a finite étale surjection `p : V ⟶ O'`
such that, with `g = p ≫ O'.ι`, every term `g^* P^q` with `a ≤ q ≤ b` is the constant sheaf of a
finite projective module, and `g^* L` is constant. -/
lemma exists_finite_etale_isConstant_model {O S : Scheme.{u}} [IrreducibleSpace O]
    [IsLocallyNoetherian O] (aO : O ⟶ S) [IsSeparated aO] [IsAffine S] {a b : ℤ}
    (P : CochainComplex (Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : IsBoundedFlatComplex Λ a b P) (hPl : ∀ q, IsFiniteLocallyConstantSheaf (P.X q))
    (L : Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hL : IsLocallyConstantSheaf L) :
    ∃ (O' : O.Opens) (_ : (O' : Set O).Nonempty) (V : Scheme.{u}) (p : V ⟶ O')
      (_ : IsFinite p) (_ : _root_.AlgebraicGeometry.Etale p) (_ : Surjective p),
      (∀ q, a ≤ q → q ≤ b → ∃ M : ModuleCat.{u + 1} Λ, Module.Projective Λ M ∧
        Module.Finite Λ M ∧ Nonempty ((constantSheaf V.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).obj M ≅ (p ≫ O'.ι)^*[ModuleCat.{u + 1} Λ].obj (P.X q))) ∧
      ((p ≫ O'.ι)^*[ModuleCat.{u + 1} Λ].obj L).IsConstant V.smallEtaleTopology := by
  let m := (b + 1 - a).toNat
  let F : Fin (m + 1) → Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    Fin.snoc (α := fun _ ↦ Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (fun i : Fin m ↦ P.X (a + (i : ℕ))) L
  obtain ⟨O', hO', V, p, hfin, het, hsurj, hc⟩ := exists_finite_etale_surjective_isConstant aO
    (m + 1) F (fun i ↦ Fin.lastCases (by simpa [F] using hL)
      (fun i ↦ by simpa [F] using (hPl _).toIsLocallyConstantSheaf) i)
  refine ⟨O', hO', V, p, hfin, het, hsurj, fun q hqa hqb ↦ ?_, by simpa [F] using hc (Fin.last m)⟩
  let g := p ≫ O'.ι
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := hO'
    obtain ⟨v, -⟩ := hsurj.surj ⟨x, hx⟩
    exact ⟨v⟩
  have hi : a + ((⟨(q - a).toNat, by omega⟩ : Fin m) : ℕ) = q := by
    simp only
    omega
  have hci := hc (Fin.castSucc ⟨(q - a).toNat, by omega⟩)
  simp only [F, Fin.snoc_castSucc, hi] at hci
  obtain ⟨⟨M, ⟨e⟩⟩⟩ := hci
  have hflat : ObjectProperty.flat ((g)^*[ModuleCat.{u + 1} Λ].obj (P.X q)) :=
    Functor.PreservesFlat.flat_obj (F := (g)^*[ModuleCat.{u + 1} Λ]) (hP.2 q)
  have : IsFiniteSheaf ((g)^*[ModuleCat.{u + 1} Λ].obj (P.X q)) := IsFiniteSheaf.upperStar _ _
  obtain ⟨h₁, h₂⟩ := projective_and_finite_of_iso_constantSheaf Λ hflat e
  exact ⟨M, h₁, h₂, ⟨e⟩⟩

omit [Finite Λ] in
/-- The right dual of a sheaf isomorphic to the constant sheaf of a finite projective module is
finite locally constant: it is the constant sheaf of the dual module, duals being unique. -/
lemma isFiniteLocallyConstantSheaf_rightDual_of_iso_constantSheaf {V : Scheme.{u}}
    {F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [HasRightDual F]
    {M : ModuleCat.{u + 1} Λ} [Module.Projective Λ M] [Module.Finite Λ M]
    (e : (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ F) :
    IsFiniteLocallyConstantSheaf Fᘁ := by
  obtain ⟨_⟩ := ModuleCat.isDualizable_of_projective M
  let C := constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let p₁ : ExactPairing F (C.obj Mᘁ) :=
    @exactPairingCongrLeft _ _ _ _ _ _ (ExactPairing.map C M Mᘁ) e.symm
  -- the dual module is finite: it is the module of linear forms
  have : Module.Finite Λ (Mᘁ : ModuleCat.{u + 1} Λ) := by
    let _ : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    have : Module.Finite Λ (M ⟶ ModuleCat.of Λ Λ) :=
      Module.Finite.equiv (ModuleCat.homLinearEquiv (S := Λ)).symm
    have : Module.Finite Λ ((ihom M).obj (𝟙_ (ModuleCat.{u + 1} Λ))) := this
    exact Module.Finite.equiv (MonoidalClosed.ihomObjUnitIso Mᘁ M).toLinearEquiv
  have := isFiniteLocallyConstantSheaf_constantSheaf (X := V) Mᘁ
  exact IsFiniteLocallyConstantSheaf.of_iso (rightDualIso p₁ inferInstance)

omit [Finite Λ] in
/-- The right dual of a zero sheaf is finite locally constant, being zero. -/
lemma isFiniteLocallyConstantSheaf_rightDual_of_isZero {V : Scheme.{u}}
    {F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [HasRightDual F] (hF : IsZero F) :
    IsFiniteLocallyConstantSheaf Fᘁ := by
  let p : ExactPairing F F :=
    { coevaluation' := 0
      evaluation' := 0
      coevaluation_evaluation' := (hF.of_iso (ρ_ F)).eq_of_src _ _
      evaluation_coevaluation' := (hF.of_iso (λ_ F)).eq_of_src _ _ }
  have := IsFiniteLocallyConstantSheaf.of_isZero hF
  exact IsFiniteLocallyConstantSheaf.of_iso (rightDualIso p inferInstance)

/-- The property of being a finite locally constant sheaf. -/
def finiteLocallyConstantSheaf (V : Scheme.{u}) :
    ObjectProperty (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsFiniteLocallyConstantSheaf F

instance (V : Scheme.{u}) : (finiteLocallyConstantSheaf Λ V).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have : IsFiniteLocallyConstantSheaf _ := h
    exact IsFiniteLocallyConstantSheaf.of_iso e

/-- A bounded-or-not complex of finite locally constant sheaves has finite locally constant
homology sheaves, `Λ` being noetherian. -/
lemma homologyProperty_Q_obj_of_isFiniteLocallyConstantSheaf {V : Scheme.{u}}
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hC : ∀ q, IsFiniteLocallyConstantSheaf (C.X q)) :
    _root_.DerivedCategory.homologyProperty (finiteLocallyConstantSheaf Λ V)
      ((_root_.DerivedCategory.Q).obj C) := fun q ↦ by
  have : IsNoetherianRing Λ := inferInstance
  have : IsFiniteLocallyConstantSheaf (C.sc q).X₁ := hC _
  have : IsFiniteLocallyConstantSheaf (C.sc q).X₂ := hC _
  have : IsFiniteLocallyConstantSheaf (C.sc q).X₃ := hC _
  have : IsFiniteLocallyConstantSheaf ((C.sc q).homology) :=
    IsFiniteLocallyConstantSheaf.homology (C.sc q)
  exact ObjectProperty.prop_of_iso _
    (((_root_.DerivedCategory.homologyFunctorFactors _ q).app C).symm) this

end Dualizable

/-! ### The Verdier dual of a complex of lisse sheaves -/

variable [Finite Λ]

/-- **The Verdier dual of a complex of lisse sheaves on a smooth scheme.** Let `O` be an
irreducible scheme, smooth of pure relative dimension `n`, separated and of finite type over a
field `k`, let `Λ` be a finite ring whose exponent is invertible in `k`, and let `P` be a bounded
complex in degrees `[a, b]` of flat finite locally constant sheaves of `Λ`-modules on `O`. Then
on a nonempty open `O' ⊆ O` the Verdier dual of `P` is bounded constructible, with Tor amplitude
in `[-b - 2n, -a - 2n]`.

On a finite étale surjection `p : V ⟶ O'` trivialising the terms of `P` and the sheaf `L` with
`ω_O ≅ L[2n]` (`proposition-exceptional-inverse-image-smooth-morphism`), `p^* = Rp^!` gives
`p^* 𝔻 P ≅ RHom(p^* P, p^* ω)`. Here `p^* P` is a bounded complex of constant sheaves of finite
projective modules, hence dualizable with dual the termwise dual complex, and `p^* ω ≅ Λ[2n]`, so
that `RHom(p^* P, p^* ω) ≅ (p^* P)^∨[2n]`: it has Tor amplitude `[-b - 2n, -a - 2n]` and finite
locally constant homology sheaves. Both properties descend along the surjection `p`. -/
theorem exists_boundedConstructible_and_torAmplitudeIn_verdierDual {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {O : Scheme.{u}} [IrreducibleSpace O]
    (aO : O ⟶ Spec (.of k)) [IsSeparated aO] [LocallyOfFiniteType aO] [QuasiCompact aO]
    (n : ℕ) [SmoothOfRelativeDimension n aO] {a b : ℤ}
    (P : CochainComplex (Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : IsBoundedFlatComplex Λ a b P) (hPl : ∀ q, IsFiniteLocallyConstantSheaf (P.X q)) :
    ∃ (O' : O.Opens) (_ : QuasiCompact O'.ι), (O' : Set O).Nonempty ∧
      boundedConstructible (ModuleCat.{u + 1} Λ) O'
        ((verdierDual Λ (O'.ι ≫ aO)).obj
          (op (D((O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P)))) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) O' (-b - 2 * n) (-a - 2 * n)
        ((verdierDual Λ (O'.ι ≫ aO)).obj
          (op (D((O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P)))) := by
  have : IsLocallyNoetherian O := LocallyOfFiniteType.isLocallyNoetherian aO
  have : HasInvertibleExponent Λ O := .of_hom aO
  -- the dualizing complex of `O` is a shifted locally constant sheaf of rank one
  obtain ⟨L, hLc, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ aO n
  obtain ⟨-, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  obtain ⟨O', hO', V, p, hfin, het, hsurj, hconst, hLV⟩ :=
    exists_finite_etale_isConstant_model Λ aO P hP hPl L hLc
  have : TopologicalSpace.NoetherianSpace O := by
    have : CompactSpace O := QuasiCompact.compactSpace_of_compactSpace aO
    have : IsNoetherian O := {}
    infer_instance
  have : TopologicalSpace.NoetherianSpace O' := O'.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact O'.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  refine ⟨O', this, hO', ?_⟩
  have : SmoothOfRelativeDimension n (O'.ι ≫ aO) := by
    have : SmoothOfRelativeDimension (0 + n) (O'.ι ≫ aO) := inferInstance
    simpa using this
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := hO'
    obtain ⟨v, -⟩ := hsurj.surj ⟨x, hx⟩
    exact ⟨v⟩
  let g := p ≫ O'.ι
  let N := D((O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P)
  let D := (verdierDual Λ (O'.ι ≫ aO)).obj (op N)
  -- the pulled-back model `P'` on `V`
  let P' := (((g)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : CochainComplex.IsStrictlyGE P' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ ((g)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 q (.inl hq))
  have : CochainComplex.IsStrictlyLE P' b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ ((g)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 q (.inr hq))
  let eN : (L((p)^*[ModuleCat.{u + 1} Λ])).obj N ≅ (_root_.DerivedCategory.Q).obj P' :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ p).app N ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app _ ≪≫
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp _ p O'.ι _ rfl).symm).app _ ≪≫
      ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app P
  have : P.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ hP.1 q (.inl hq)
  have : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ hP.1 q (.inr hq)
  have hQt : torAmplitudeIn (ModuleCat.{u + 1} Λ) O a b ((_root_.DerivedCategory.Q).obj P) :=
    _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b hP.2
  have hNt : torAmplitudeIn (ModuleCat.{u + 1} Λ) V a b ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N) :=
    torAmplitudeIn_leftDerivedUpperStar _ p a b ((torAmplitudeIn _ O' a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ O'.ι).app _)
      (torAmplitudeIn_leftDerivedUpperStar _ O'.ι a b hQt))
  -- the pulled-back dualizing complex is `Λ[2n]`
  let eω' : (R(p)^![Λ]).obj (dualizingComplex _ (O'.ι ≫ aO)) ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((g)^*[ModuleCat.{u + 1} Λ].obj L))⟦(2 * n : ℤ)⟧ :=
    (rightDerivedUpperShriekIsoOfIsFiniteOfEtale _ p).app _ ≪≫
      D((p)^*[ModuleCat.{u + 1} Λ]).mapIso
        ((nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ O'.ι aO).some.symm ≪≫
          (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ O'.ι).app _ ≪≫
          D((O'.ι)^*[ModuleCat.{u + 1} Λ]).mapIso eω ≪≫
          (D((O'.ι)^*[ModuleCat.{u + 1} Λ]).commShiftIso (2 * n : ℤ)).app _ ≪≫
          (shiftFunctor _ (2 * n : ℤ)).mapIso
            ((((O'.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app L)) ≪≫
      (D((p)^*[ModuleCat.{u + 1} Λ]).commShiftIso (2 * n : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * n : ℤ)).mapIso
        ((((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((Etale.upperStarComp _ p O'.ι _ rfl).app L).symm)
  have hωt : torAmplitudeIn (ModuleCat.{u + 1} Λ) V (-(2 * n)) (-(2 * n))
      ((R(p)^![Λ]).obj (dualizingComplex _ (O'.ι ≫ aO))) := by
    have h := torAmplitudeIn_shift _ (torAmplitudeIn_singleFunctor_zero_of_flat _ _
      (Functor.PreservesFlat.flat_obj (F := (g)^*[ModuleCat.{u + 1} Λ]) hLf)) (2 * n : ℤ)
    exact (torAmplitudeIn _ V _ _).prop_of_iso eω'.symm (by simpa using h)
  -- `p^* 𝔻 N ≅ RHom(p^* N, Rp^! ω)`
  obtain ⟨eH⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ p N
    (dualizingComplex _ (O'.ι ≫ aO))
  let eD : D((p)^*[ModuleCat.{u + 1} Λ]).obj D ≅
      ((RHom(V)[ModuleCat.{u + 1} Λ]).obj (op ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(p)^![Λ]).obj (dualizingComplex _ (O'.ι ≫ aO))) :=
    ((rightDerivedUpperShriekIsoOfIsFiniteOfEtale _ p).app _).symm ≪≫ eH
  have hPd : ∀ q, IsDualizable (P'.X q) := by
    intro q
    by_cases hqa : a ≤ q
    · by_cases hqb : q ≤ b
      · obtain ⟨M, hproj, hfinite, ⟨e⟩⟩ := hconst q hqa hqb
        exact IsDualizable.of_iso e (isDualizable_constantSheaf Λ M)
      · exact CategoryTheory.IsZero.isDualizable
          (((g)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 q (.inr (by omega))))
    · exact CategoryTheory.IsZero.isDualizable
        (((g)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 q (.inl (by omega))))
  -- the Tor amplitude
  have hDt : torAmplitudeIn (ModuleCat.{u + 1} Λ) O' (-b - 2 * n) (-a - 2 * n) D := by
    have hNd : IsDualizable ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N) :=
      IsDualizable.of_iso eN.symm (_root_.DerivedCategory.isDualizable_Q_obj P' a b hPd)
    have h := torAmplitudeIn_derivedHom_of_isDualizable_aux _ hNt hNd hωt
    refine torAmplitudeIn_of_leftDerivedUpperStar_of_surjective Λ p hsurj.surj ?_
    refine (torAmplitudeIn _ V _ _).prop_of_iso
      (eD.symm ≪≫ ((leftDerivedUpperStarIsoMapDerivedCategory _ p).app _).symm) ?_
    exact h.mono (by omega) (by omega)
  -- On the cover the dualizing line is the unit, so the dual is the shifted termwise dual.
  let : ∀ q, HasRightDual (P'.X q) := fun q ↦ (hPd q).some
  obtain ⟨pair⟩ := _root_.DerivedCategory.nonempty_exactPairing_Q_obj P' a b
  let := pair
  obtain ⟨_⟩ := nonempty_exactPairing_swap ((_root_.DerivedCategory.Q).obj P')
    ((_root_.DerivedCategory.Q).obj (CochainComplex.rightDual P'))
  obtain ⟨v⟩ := ‹Nonempty V›
  let t := V.algClosurePoint v
  have hLV' : ((g)^*[ModuleCat.{u + 1} Λ].obj L).IsConstant V.smallEtaleTopology := hLV
  obtain ⟨eL⟩ := nonempty_iso_unit_of_isConstant ((g)^*[ModuleCat.{u + 1} Λ].obj L) t
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g t).app L ≪≫ (hLs _ (t ≫ g)).some)
  let H := (RHom(V)[ModuleCat.{u + 1} Λ]).obj (op ((_root_.DerivedCategory.Q).obj P'))
  let eModel : D((p)^*[ModuleCat.{u + 1} Λ]).obj D ≅
      ((_root_.DerivedCategory.Q).obj (CochainComplex.rightDual P'))⟦(2 * n : ℤ)⟧ :=
    eD ≪≫ ((RHom(V)[ModuleCat.{u + 1} Λ]).mapIso eN.op.symm).app _ ≪≫
      H.mapIso (eω' ≪≫ (shiftFunctor _ (2 * n : ℤ)).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso eL ≪≫
          singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) V)) ≪≫
      (H.commShiftIso (2 * n : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * n : ℤ)).mapIso
        (MonoidalClosed.ihomObjUnitIso
          ((_root_.DerivedCategory.Q).obj (CochainComplex.rightDual P'))
          ((_root_.DerivedCategory.Q).obj P'))
  have hDual : ∀ q, IsFiniteLocallyConstantSheaf ((CochainComplex.rightDual P').X q) := by
    intro q
    change IsFiniteLocallyConstantSheaf (P'.X (-q))ᘁ
    by_cases hqa : a ≤ -q
    · by_cases hqb : -q ≤ b
      · obtain ⟨M, hproj, hfinite, ⟨e⟩⟩ := hconst (-q) hqa hqb
        exact isFiniteLocallyConstantSheaf_rightDual_of_iso_constantSheaf Λ e
      · exact isFiniteLocallyConstantSheaf_rightDual_of_isZero Λ
          (((g)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 (-q) (.inr (by omega))))
    · exact isFiniteLocallyConstantSheaf_rightDual_of_isZero Λ
        (((g)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 (-q) (.inl (by omega))))
  have hhom := homologyProperty_Q_obj_of_isFiniteLocallyConstantSheaf Λ
    (CochainComplex.rightDual P') hDual
  have hshift := (_root_.DerivedCategory.homologyProperty
    (finiteLocallyConstantSheaf Λ V)).le_shift (2 * n : ℤ) _ hhom
  have hcover := (_root_.DerivedCategory.homologyProperty
    (finiteLocallyConstantSheaf Λ V)).prop_of_iso eModel.symm hshift
  refine ⟨⟨?_, fun q ↦ ?_⟩, hDt⟩
  · exact (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded D).1
      ⟨_, _, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hDt⟩
  · have : IsFiniteLocallyConstantSheaf
        ((p)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj D)) :=
      (finiteLocallyConstantSheaf Λ V).prop_of_iso
        ((((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app D).symm
        (hcover q)
    exact IsFiniteLocallyConstantSheaf.isConstructibleSheaf
      (IsFiniteLocallyConstantSheaf.of_upperStar_of_etale p _)

end Etale

end AlgebraicGeometry
