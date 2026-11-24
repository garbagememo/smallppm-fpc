program smallppm_tthread;

{$MODE objfpc}{$H+}
{$INLINE ON}
{$modeswitch advancedrecords}
{$codepage utf8} // ← これを追加！

uses
  {$ifdef unix}
  cthreads, cmem, cwstring,
  {$endif}
  Classes, SysUtils, Math, FPImage, syncobjs, uVect, uBMP;

const
  ALPHA = 0.7;

type
  TReflType = (DIFF, SPEC, REFR);

  TAABB = record
    min_pt, max_pt: Vec3;
    procedure fit(const p: Vec3); inline;
    procedure reset; inline;
  end;

  PHPoint = ^THPoint;
  THPoint = record
    f, pos, nrm, flux: Vec3;
    r2: Double;
    n: Cardinal; // N / ALPHA
    pix: Integer;
  end;

  PList = ^TListNode;
  TListNode = record
    id: PHPoint;
    next: PList;
  end;

  TSphere = record
    rad: Double;
    p, c: Vec3;
    refl: TReflType;
    function intersect(const r: RayRecord): Double; inline;
  end;

  THitPassContext = record
    w, h: Integer;
    cam: RayRecord;
    cx, cy: Vec3;
    row_lists: array of PList;
    next_row: LongInt;
    done_rows: LongInt;
  end;
  PHitPassContext=^THitPassContext;

  THitPointThread = class(TThread)
  private
    FCtx: PHitPassContext;
  protected
    procedure Execute; override;
  public
    constructor Create(ACtx: PHitPassContext);
  end;

  
  TPhotonThread = class(TThread)
  private
    FNextBatch: ^LongInt;
    FTotalBatches: Integer;
  protected
    procedure Execute; override;
  public
    constructor Create(ANextBatch: PLongInt; ATotalBatches: Integer);
  end;

const
  Primes: array[0..60] of Integer = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
    83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283
  );

  Spheres: array[0..8] of TSphere = (
    (rad: 1e5;  p: (x:  1e5 + 1; y: 40.8;      z: 81.6); c: (x: 0.75;  y: 0.25;  z: 0.25); refl: DIFF), // Left
    (rad: 1e5;  p: (x: -1e5 + 99; y: 40.8;      z: 81.6); c: (x: 0.25;  y: 0.25;  z: 0.75); refl: DIFF), // Right
    (rad: 1e5;  p: (x: 50;       y: 40.8;      z: 1e5);  c: (x: 0.75;  y: 0.75;  z: 0.75); refl: DIFF), // Back
    (rad: 1e5;  p: (x: 50;       y: 40.8;      z: -1e5 + 170); c: (x: 0; y: 0;    z: 0);    refl: DIFF), // Front
    (rad: 1e5;  p: (x: 50;       y: 1e5;       z: 81.6); c: (x: 0.75;  y: 0.75;  z: 0.75); refl: DIFF), // Bottom
    (rad: 1e5;  p: (x: 50;       y: -1e5 + 81.6; z: 81.6); c: (x: 0.75; y: 0.75; z: 0.75); refl: DIFF), // Top
    (rad: 16.5; p: (x: 27;       y: 16.5;      z: 47);   c: (x: 0.999; y: 0.999; z: 0.999); refl: SPEC), // Mirror
    (rad: 16.5; p: (x: 73;       y: 16.5;      z: 88);   c: (x: 0.999; y: 0.999; z: 0.999); refl: REFR), // Glass
    (rad: 8.5;  p: (x: 50;       y: 8.5;       z: 60);   c: (x: 0.999; y: 0.999; z: 0.999); refl: DIFF)  // Middle
  );

var
  num_hash, num_photon: Cardinal;
  hash_s: Double;
  hash_grid: array of PList;
  hitpoints: PList = nil;
  hpbbox: TAABB;
  io_lock: TCriticalSection;
  photon_done: LongInt = 0;

function rev(const i, p: Integer): Integer; inline;
begin
  if i = 0 then
    Result := i
  else
    Result := p - i;
end;

function hal(const b: Integer; j: Int64): Double;
var
  p: Integer;
  h, f, fct: Double;
begin
  p := Primes[b];
  h := 0.0;
  f := 1.0 / Double(p);
  fct := f;
  while j > 0 do
  begin
    h := h + rev(j mod p, p) * fct;
    j := j div p;
    fct := fct * f;
  end;
  Result := h;
end;

procedure TAABB.fit(const p: Vec3);
begin
  if p.x < min_pt.x then min_pt.x := p.x;
  if p.y < min_pt.y then min_pt.y := p.y;
  if p.z < min_pt.z then min_pt.z := p.z;
  if p.x > max_pt.x then max_pt.x := p.x;
  if p.y > max_pt.y then max_pt.y := p.y;
  if p.z > max_pt.z then max_pt.z := p.z;
end;

procedure TAABB.reset;
begin
  min_pt := Vec3.new(INF, INF, INF);
  max_pt := Vec3.new(-INF, -INF, -INF);
end;

function ListAdd(i: PHPoint; h: PList): PList; inline;
var
  p: PList;
begin
  New(p);
  p^.id := i;
  p^.next := h;
  Result := p;
end;

function hash_idx(const ix, iy, iz: Integer): Cardinal; inline;
var
  h: Int64;
begin
  h := (Int64(ix) * 73856093) xor (Int64(iy) * 19349663) xor (Int64(iz) * 83492791);
  Result := Cardinal(h) mod num_hash;
end;

procedure build_hash_grid(const w, h: Integer);
var
  lst: PList;
  hp: PHPoint;
  ssize, BMin, BMax: Vec3;
  irad: Double;
  vphoton, ix, iy, iz: Integer;
  i, hv: Cardinal;
begin
  hpbbox.reset;
  lst := hitpoints;
  while lst <> nil do
  begin
    hp := lst^.id;
    lst := lst^.next;
    hpbbox.fit(hp^.pos);
  end;

  ssize := hpbbox.max_pt - hpbbox.min_pt;
  irad := ((ssize.x + ssize.y + ssize.z) / 3.0) / ((w + h) / 2.0) * 2.0;

  hpbbox.reset;
  lst := hitpoints;
  vphoton := 0;
  while lst <> nil do
  begin
    hp := lst^.id;
    lst := lst^.next;
    hp^.r2 := irad * irad;
    hp^.n := 0;
    hp^.flux := ZeroVec;
    Inc(vphoton);
    hpbbox.fit(hp^.pos - irad);
    hpbbox.fit(hp^.pos + irad);
  end;

  hash_s := 1.0 / (irad * 2.0);
  num_hash := Cardinal(vphoton);

  SetLength(hash_grid, num_hash);
  for i := 0 to num_hash - 1 do
    hash_grid[i] := nil;

  lst := hitpoints;
  while lst <> nil do
  begin
    hp := lst^.id;
    lst := lst^.next;
    BMin := ((hp^.pos - irad) - hpbbox.min_pt) * hash_s;
    BMax := ((hp^.pos + irad) - hpbbox.min_pt) * hash_s;
    for iz := Abs(Trunc(BMin.z)) to Abs(Trunc(BMax.z)) do
      for iy := Abs(Trunc(BMin.y)) to Abs(Trunc(BMax.y)) do
        for ix := Abs(Trunc(BMin.x)) to Abs(Trunc(BMax.x)) do
        begin
          hv := hash_idx(ix, iy, iz);
          hash_grid[hv] := ListAdd(hp, hash_grid[hv]);
        end;
  end;
end;

function TSphere.intersect(const r: RayRecord): Double;
var
  op: Vec3;
  t, b, det: Double;
begin
  op := p - r.o;
  b := op * r.d;
  det := b * b - (op * op) + rad * rad;
  if det < 0 then
  begin
    Result := INF;
    Exit;
  end;
  det := Sqrt(det);
  t := b - det;
  if t > eps then
    Result := t
  else
  begin
    t := b + det;
    if t > eps then
      Result := t
    else
      Result := INF;
  end;
end;

function scene_intersect(const r: RayRecord; out t: Double; out id: Integer): Boolean;
var
  i: Integer;
  d: Double;
begin
  t := INF;
  id := -1;
  for i := Low(Spheres) to High(Spheres) do
  begin
    d := Spheres[i].intersect(r);
    if d < t then
    begin
      t := d;
      id := i;
    end;
  end;
  Result := t < INF;
end;

procedure genp(var pr: RayRecord; var f: Vec3; i: Integer);
var
  p, t, st: Double;
begin
  f := Vec3.new(2500, 2500, 2500) * (Pi * 4.0);
  p := 2.0 * Pi * hal(0, i);
  t := 2.0 * ArcCos(Sqrt(1.0 - hal(1, i)));
  st := Sin(t);
  pr.d := Vec3.new(Cos(p) * st, Cos(t), Sin(p) * st);
  pr.o := Vec3.new(50, 60, 85);
end;

procedure trace(const r: RayRecord; dpt: Integer; m: Boolean; const fl, adj: Vec3;
  i, pix_idx: Integer; var local_list: PList);
var
  t: Double;
  id, d3, ix, iy, iz: Integer;
  obj: TSphere;
  x, n, f, nl, w, u, v, d, hh, diff_vec, td, fa: Vec3;
  p, r1, r2, r2s, g, nc, nt, nnt, ddn, cos2t, a, b, R0, c_val, Re, P_prob, sgn: Double;
  hp: PHPoint;
  node: PList;
  hitpoint: PHPoint;
  into: Boolean;
  lr, rr: RayRecord;
begin
  Inc(dpt);
  if (not scene_intersect(r, t, id)) or (dpt >= 20) then
    Exit;

  d3 := dpt * 3;
  obj := Spheres[id];
  x := r.o + r.d * t;
  n := (x - obj.p).Norm;
  f := obj.c;

  if (n * r.d) < 0 then
    nl := n
  else
    nl := n * -1.0;

  if (f.x > f.y) and (f.x > f.z) then
    p := f.x
  else if f.y > f.z then
    p := f.y
  else
    p := f.z;

  if obj.refl = DIFF then
  begin
    r1 := 2.0 * Pi * hal(d3 - 1, i);
    r2 := hal(d3 + 0, i);
    r2s := Sqrt(r2);
    w := nl;
    if Abs(w.x) > 0.1 then
      u := (Vec3.new(0, 1, 0) / w).Norm
    else
      u := (Vec3.new(1, 0, 0) / w).Norm;
    v := w / u;
    d := (u * (Cos(r1) * r2s) + v * (Sin(r1) * r2s) + w * Sqrt(1.0 - r2)).Norm;

    if m then
    begin
      New(hp);
      hp^.f := f.Mult(adj);
      hp^.pos := x;
      hp^.nrm := n;
      hp^.flux := ZeroVec;
      hp^.r2 := 0;
      hp^.n := 0;
      hp^.pix := pix_idx;
      local_list := ListAdd(hp, local_list);
    end
    else
    begin
      hh := (x - hpbbox.min_pt) * hash_s;
      ix := Abs(Trunc(hh.x));
      iy := Abs(Trunc(hh.y));
      iz := Abs(Trunc(hh.z));

      node := hash_grid[hash_idx(ix, iy, iz)];
      while node <> nil do
      begin
        hitpoint := node^.id;
        node := node^.next;
        diff_vec := hitpoint^.pos - x;
        if ((hitpoint^.nrm * n) > 1e-3) and ((diff_vec * diff_vec) <= hitpoint^.r2) then
        begin
          g := (hitpoint^.n * ALPHA + ALPHA) / (hitpoint^.n * ALPHA + 1.0);
          hitpoint^.r2 := hitpoint^.r2 * g;
          Inc(hitpoint^.n);
          hitpoint^.flux := (hitpoint^.flux + hitpoint^.f.Mult(fl) * (1.0 / Pi)) * g;
        end;
      end;

      if hal(d3 + 1, i) < p then
        trace(RayRecord.new(x, d), dpt, m, f.Mult(fl) * (1.0 / p), adj, i, pix_idx, local_list);
    end;
  end
  else if obj.refl = SPEC then
  begin
    trace(RayRecord.new(x, r.d - n * (2.0 * (n * r.d))), dpt, m, f.Mult(fl), f.Mult(adj), i, pix_idx, local_list);
  end
  else
  begin
    lr := RayRecord.new(x, r.d - n * (2.0 * (n * r.d)));
    into := (n * nl) > 0.0;
    nc := 1.0;
    nt := 1.5;
    if into then
      nnt := nc / nt
    else
      nnt := nt / nc;

    ddn := r.d * nl;
    cos2t := 1.0 - nnt * nnt * (1.0 - ddn * ddn);

    if cos2t < 0 then
    begin
      trace(lr, dpt, m, fl, adj, i, pix_idx, local_list);
      Exit;
    end;

    if into then sgn := 1.0 else sgn := -1.0;
    td := (r.d * nnt - n * (sgn * (ddn * nnt + Sqrt(cos2t)))).Norm;

    a := nt - nc;
    b := nt + nc;
    R0 := (a * a) / (b * b);
    if into then
      c_val := 1.0 - (-ddn)
    else
      c_val := 1.0 - (td * n);

    Re := R0 + (1.0 - R0) * c_val * c_val * c_val * c_val * c_val;
    P_prob := Re;
    rr := RayRecord.new(x, td);
    fa := f.Mult(adj);

    if m then
    begin
      trace(lr, dpt, m, fl, fa * Re, i, pix_idx, local_list);
      trace(rr, dpt, m, fl, fa * (1.0 - Re), i, pix_idx, local_list);
    end
    else
    begin
      if hal(d3 - 1, i) < P_prob then
        trace(lr, dpt, m, fl, fa, i, pix_idx, local_list)
      else
        trace(rr, dpt, m, fl, fa, i, pix_idx, local_list);
    end;
  end;
end;

constructor THitPointThread.Create(ACtx: PHitPassContext);
begin
  inherited Create(True);
  FreeOnTerminate := False;
  FCtx := ACtx;
end;

procedure THitPointThread.Execute;
var
  y, x, pix_idx: Integer;
  d: Vec3;
  row_head: PList;
  cur_done: LongInt;
begin
  while True do
  begin
    y := InterlockedIncrement(FCtx^.next_row) - 1;
    if y >= FCtx^.h then
      Break;

    row_head := nil;
    for x := 0 to FCtx^.w - 1 do
    begin
      pix_idx := x + y * FCtx^.w;
      d := FCtx^.cx * ((x + 0.5) / FCtx^.w - 0.5) +
           FCtx^.cy * (-(y + 0.5) / FCtx^.h + 0.5) +
           FCtx^.cam.d;
      trace(RayRecord.new(FCtx^.cam.o + d * 140, d.Norm), 0, True,
            ZeroVec, Vec3.new(1, 1, 1), 0, pix_idx, row_head);
    end;
    FCtx^.row_lists[y] := row_head;

    cur_done := InterlockedIncrement(FCtx^.done_rows);
    if (cur_done mod 16 = 0) or (cur_done = FCtx^.h) then
    begin
      io_lock.Acquire;
      try
        Write(Format(#13'HitPointPass %5.2f%%', [100.0 * cur_done / FCtx^.h]));
      finally
        io_lock.Release;
      end;
    end;
  end;
end;

constructor TPhotonThread.Create(ANextBatch: PLongInt; ATotalBatches: Integer);
begin
  inherited Create(True);
  FreeOnTerminate := False;
  FNextBatch := ANextBatch;
  FTotalBatches := ATotalBatches;
end;

procedure TPhotonThread.Execute;
var
  batch_idx, m, j: Integer;
  r: RayRecord;
  f: Vec3;
  dummy_list: PList;
  cur_done: LongInt;
begin
  dummy_list := nil;
  while True do
  begin
    batch_idx := InterlockedIncrement(FNextBatch^) - 1;
    if batch_idx >= FTotalBatches then
      Break;

    m := 1000 * batch_idx;
    for j := 0 to 999 do
    begin
      genp(r, f, m + j);
      trace(r, 0, False, f, Vec3.new(1, 1, 1), m + j, 0, dummy_list);
    end;

    cur_done := InterlockedIncrement(photon_done);
    if (cur_done mod 16 = 0) or (cur_done = FTotalBatches) then
    begin
      io_lock.Acquire;
      try
        Write(Format(#13'PhotonPass %5.2f%%', [100.0 * cur_done / FTotalBatches]));
      finally
        io_lock.Release;
      end;
    end;
  end;
end;

procedure RunHitPointPassParallel(var ctx: THitPassContext; thread_count: Integer);
var
  threads: array of THitPointThread;
  i: Integer;
begin
  SetLength(threads, thread_count);
  for i := 0 to thread_count - 1 do
    threads[i] := THitPointThread.Create(@ctx);
  try
    for i := 0 to thread_count - 1 do
      threads[i].Start;
    for i := 0 to thread_count - 1 do
      threads[i].WaitFor;
  finally
    for i := 0 to thread_count - 1 do
      threads[i].Free;
  end;
end;

procedure RunPhotonPassParallel(total_batches, thread_count: Integer);
var
  threads: array of TPhotonThread;
  next_batch: LongInt;
  i: Integer;
begin
  next_batch := 0;
  photon_done := 0;
  SetLength(threads, thread_count);
  for i := 0 to thread_count - 1 do
    threads[i] := TPhotonThread.Create(@next_batch, total_batches);
  try
    for i := 0 to thread_count - 1 do
      threads[i].Start;
    for i := 0 to thread_count - 1 do
      threads[i].WaitFor;
  finally
    for i := 0 to thread_count - 1 do
      threads[i].Free;
  end;
end;

procedure MergeRowLists(var ctx: THitPassContext);
var
  y: Integer;
  node, next_node: PList;
begin
  hitpoints := nil;
  for y := 0 to ctx.h - 1 do
  begin
    node := ctx.row_lists[y];
    while node <> nil do
    begin
      next_node := node^.next;
      node^.next := hitpoints;
      hitpoints := node;
      node := next_node;
    end;
  end;
end;

var
  w, h, samps, x, y, idx, thread_count: Integer;
  c: array of Vec3;
  lst: PList;
  hp: PHPoint;
  bmp: BMPRecord;
  hit_ctx: THitPassContext;
begin
  w := 1024;
  h := 768;
  if ParamCount >= 1 then
    samps := Max(StrToIntDef(ParamStr(1), 1000000) div 1000, 1)
  else
    samps := 1000;

  thread_count := Max(GetCPUCount, 1);

  io_lock := TCriticalSection.Create;
  try
    SetLength(c, w * h);
    for idx := 0 to w * h - 1 do
      c[idx] := ZeroVec;

    hit_ctx.w := w;
    hit_ctx.h := h;
    hit_ctx.cam := RayRecord.new(Vec3.new(50, 48, 295.6), Vec3.new(0, -0.042612, -1).Norm);
    hit_ctx.cx := Vec3.new(w * 0.5135 / h, 0, 0);
    hit_ctx.cy := ((hit_ctx.cx / hit_ctx.cam.d).Norm) * 0.5135;
    SetLength(hit_ctx.row_lists, h);
    for y := 0 to h - 1 do
      hit_ctx.row_lists[y] := nil;
    hit_ctx.next_row := 0;
    hit_ctx.done_rows := 0;

    RunHitPointPassParallel(hit_ctx, thread_count);
    MergeRowLists(hit_ctx);
    WriteLn;

    build_hash_grid(w, h);

    num_photon := Cardinal(samps);
    RunPhotonPassParallel(Integer(num_photon), thread_count);
    WriteLn;

    lst := hitpoints;
    while lst <> nil do
    begin
      hp := lst^.id;
      lst := lst^.next;
      idx := hp^.pix;
      c[idx] := c[idx] + hp^.flux * (1.0 / (Pi * hp^.r2 * num_photon * 1000.0));
    end;

    bmp.new(w, h);
    for y := 0 to h - 1 do
      for x := 0 to w - 1 do
      begin
        idx := x + y * w;
        bmp.SetPixel(x, y, ColToRGB(Vec3.new(
          1.0 - Exp(-c[idx].x),
          1.0 - Exp(-c[idx].y),
          1.0 - Exp(-c[idx].z)
        )));
      end;

    bmp.WriteFile('image.ppm');
  finally
    io_lock.Free;
  end;
end.
