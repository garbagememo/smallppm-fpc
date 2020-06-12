UNIT WriteBMP;
{$MODE objfpc}{$H+}
INTERFACE
Uses Classes,SysUtils;

CONST
    MaxArrayNum=1024*1024*2*2;
    AllocMemSize=1024*1024*3+5120;

TYPE
    rgbColor=record b,g,r:byte; end;

    BMPArray=ARRAY[0..MaxArrayNum*3] OF BYTE;
    BMPIOClass=Class
      bmpBodySize:longint;
      BMPWidth,BMPHeight:longint;
      bmpfileheader : packed array[0..14-1] of byte;
      bmpinfoheader : packed array[0..40-1] of byte;
      bmpBody:BMPArray;
      constructor Create(x,y:integer);virtual;
      procedure SetPixel(x,y:integer;col:rgbColor);
      procedure WriteBMPFile(FN:string);
    end;
IMPLEMENTATION
constructor BMPIOClass.Create(x,y:longint);
var
  headersize, bfSize : longint;
  bits_per_pixel, cmap_entries : integer;
  i:integer;
begin
   BMPWidth:=x;BMPHeight:=y;
   bits_per_pixel := 24;
   cmap_entries := 0;
   headersize:=14+40;
   bfsize:=headersize+longint(x*y)*3;
   bmpBodySize:=bfSize;
   for i:=0 to 14-1 do bmpfileheader[i]:=0;
   for i:=0 to 40-1 do bmpinfoheader[i]:=0;

  { Fill the file header }
   bmpfileheader[0] := $42;	{ first 2 bytes are ASCII 'B', 'M' }
   bmpfileheader[1] := $4D;
  {PUT_4B(bmpfileheader, 2, bfSize);} { bfSize }
	 bmpfileheader[2] := byte ((bfSize) and $FF);
	 bmpfileheader[2+1] := byte (((bfSize) shr 8) and $FF);
	 bmpfileheader[2+2] := byte (((bfSize) shr 16) and $FF);
	 bmpfileheader[2+3] := byte (((bfSize) shr 24) and $FF);
  { we leave bfReserved1 & bfReserved2 = 0 }
  {PUT_4B(bmpfileheader, 10, headersize);} { bfOffBits }
	 bmpfileheader[10] := byte (headersize and $FF);
	 bmpfileheader[10+1] := byte ((headersize shr 8) and $FF);
	 bmpfileheader[10+2] := byte ((headersize shr 16) and $FF);
	 bmpfileheader[10+3] := byte ((headersize shr 24) and $FF);

  { Fill the info header (Microsoft calls this a BITMAPINFOHEADER) }
  {PUT_2B(bmpinfoheader, 0, 40);}   { biSize }
	 bmpinfoheader[0] := byte ((40) and $FF);
	 bmpinfoheader[0+1] := byte (((40) shr 8) and $FF);

  {PUT_4B(bmpinfoheader, 4, cinfo^.output_width);} { biWidth }
         bmpinfoheader[4] := byte ((x) and $FF);
         bmpinfoheader[4+1] := byte ((x shr 8) and $FF);
         bmpinfoheader[4+2] := byte ((x shr 16) and $FF);
         bmpinfoheader[4+3] := byte ((x shr 24) and $FF);
  {PUT_4B(bmpinfoheader, 8, cinfo^.output_height);} { biHeight }
         bmpinfoheader[8] := byte (y and $FF);
         bmpinfoheader[8+1] := byte ((y shr 8) and $FF);
         bmpinfoheader[8+2] := byte ((y shr 16) and $FF);
         bmpinfoheader[8+3] := byte ((y shr 24) and $FF);
  {PUT_2B(bmpinfoheader, 12, 1);}	{ biPlanes - must be 1 }
         bmpinfoheader[12] := byte (1 and $FF);
         bmpinfoheader[12+1] := byte ((1 shr 8) and $FF);

  {PUT_2B(bmpinfoheader, 14, bits_per_pixel);} { biBitCount }
         bmpinfoheader[14] := byte (bits_per_pixel and $FF);
         bmpinfoheader[14+1] := byte ((bits_per_pixel shr 8) and $FF);
  { we leave biCompression = 0, for none }
  { we leave biSizeImage = 0; this is correct for uncompressed data }
  { we leave biClrImportant := 0 }

end;

procedure BMPIOClass.SetPixel(x,y:integer;col:rgbColor);
begin
   bmpBody[(y*BMPWidth+x)*3  ]:=col.b;
   bmpBody[(y*BMPWidth+x)*3+1]:=col.g;
   bmpBody[(y*BMPWidth+x)*3+2]:=col.r;

end;

procedure BMPIOClass.WriteBMPFile(FN:string);
var
   B : file;
begin
   Assign(B,FN);rewrite(B,1);
   BlockWrite(B,bmpfileheader,14);
   Blockwrite(B,bmpInfoheader,40);
   blockwrite(b,bmpBody,bmpBodySize);
    Close(b);
end;


BEGIN
END.
{ test code

var
   BMPIO : BMPIOClass;
   Vcolor : rgbColor;
   yAxis,xAxis: integer;
begin
   Vcolor.r:=$FF;Vcolor.g:=$0;Vcolor.b:=0;
   BMPIO:=BMPIOClass.Create(512,512);
   for yAxis:=0 to BMPIO.bmpHeight-1 do
      for xAxis:=0 to BMPIO.bmpWidth-1 do begin
	 vColor.r:= round( (yAxis/BMPIO.bmpWidth) *255);
	 vColor.g:=round((xAxis/BMPIO.bmpHeight)*255);
         vColor.b:=128;
         BMPIO.SetPixel(xAxis,yAxis,vColor);
      end;
    BMPIO.WriteBMPFile('test.bmp');
end.
//$Log: WriteBMP.pas,v $
//Revision 1.3  2017/08/27 06:30:43  average
//上下反転にした
//
//Revision 1.2  2017/08/26 14:50:31  average
//Unixのビットマップと違うみたいなので、上下を反転
//
//Revision 1.1  2016/11/22 16:03:11  average
//Initial revision
//

//
}
