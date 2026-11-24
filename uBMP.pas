unit uBMP;
{$MODE objfpc}{$H+}
{$modeswitch advancedrecords}
{$codepage utf8} // ← これを追加！
interface
uses
   classes,SysUtils,math,FPImage,
   FPWritePNM,FPWritePNG,FPWriteBMP,
   FPReadPNG,FPReadJPEG,FPReadPNM,FPReadBMP;

type
   BMPRecord=record
      image:TFPMemoryImage;
      procedure new(x,y:integer);
      procedure SetPixel(x,y:integer;col:TFPColor);
      function GetPixel(x,y:integer):TFPColor;
      
      // 自動判定用の統一書き出しメソッド
      procedure WriteFile(FN: string);
      
      // 統一読み込みメソッド
      procedure ReadFile(FN:String);
   end;

implementation

procedure BMPRecord.new(x,y:longint);
begin
   image := TFPMemoryImage.Create (x,y);
end;

procedure BMPRecord.SetPixel(x,y:integer;col:TFPColor);
begin
   image.colors[x,y]:=col;
end;

function BMPRecord.GetPixel(x,y:integer):TFPColor;
begin
   result:=image.colors[x,y];
end;

// ----------------------------------------------------
// 拡張子から判別して自動で適切な出力を行うメソッド
// ----------------------------------------------------
procedure BMPRecord.WriteFile(FN: string);
var
   Ext: String;
   Writer: TFPCustomImageWriter;
begin
   
   Ext := LowerCase(ExtractFileExt(FN));
   Writer := nil;

   // 拡張子判定でライターを選択
   if (Ext = '.ppm') or (Ext = '.pnm') then begin
      Writer := TFPWriterPNM.Create;
      TFPWriterPNM(Writer).BinaryFormat := false;
   end
   else if Ext = '.png' then begin
      Writer := TFPWriterPNG.Create;
      TFPWriterPNG(Writer).WordSized:=false;
   end
   else if Ext = '.bmp' then begin
      Writer := TFPWriterBMP.Create;
   end
   else begin
      WriteLn('未対応の拡張子のためファイル名をout.pngに ');
      FN:='out.png';
      Writer := TFPWriterPNG.Create;
      TFPWriterPNG(Writer).WordSized:=false;
   end;

   try
      WriteLn('保存中: ', FN, ' (フォーマット: ', UpperCase(Copy(Ext, 2, Length(Ext))), ')');
      Image.SaveToFile(FN, Writer);
      WriteLn('保存が完了しました。');
   finally
      Writer.Free;
   end;
end;


procedure BMPRecord.ReadFile(FN:string);
var
   Ext:string;
   reader : TFPCustomImageReader;
begin
   Image := TFPMemoryImage.Create(0, 0);
   Ext := LowerCase(ExtractFileExt(FN));
   reader := nil;

   // 拡張子判定でリーダーを選択
   if Ext='.ppm' then begin
      reader:=TFPReaderPNM.Create;
   end
   else if Ext = '.png' then begin
      reader := TFPReaderPNG.Create;
   end
   else if Ext='.jpg' then begin
      reader:=TFPReaderJPEG.Create;
   end
   else if Ext = '.bmp' then
      reader := TFPReaderBMP.Create
   else
   begin
      WriteLn('未対応の拡張子のため中止 ');
      Halt(0);
   end;
   try
      Image.LoadFromFile(FN, reader);
   except
      on E: Exception do
         WriteLn('Error loading file: ', E.Message);
   end;

   reader.Free;
end;


begin
end.
