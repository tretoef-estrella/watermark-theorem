// cold reader's own PDF helper: text extraction and page rendering via PDFKit
import Foundation
import PDFKit
import AppKit
let a = CommandLine.arguments
// usage: pdftool text file.pdf out.txt | render file.pdf page(1-based) out.png scale
guard a.count >= 4, let doc = PDFDocument(url: URL(fileURLWithPath: a[2])) else { print("usage/err"); exit(1) }
if a[1] == "text" {
  var s = ""
  for i in 0..<doc.pageCount { s += "\n=====PAGE \(i+1)\n" + (doc.page(at: i)?.string ?? "") }
  try! s.write(toFile: a[3], atomically: true, encoding: .utf8)
  print("pages", doc.pageCount)
} else {
  let pn = Int(a[3])! - 1
  let scale = CGFloat(Double(a.count > 5 ? a[5] : "2.0")!)
  let page = doc.page(at: pn)!
  let b = page.bounds(for: .mediaBox)
  let w = Int(b.width*scale), h = Int(b.height*scale)
  let rep = NSBitmapImageRep(bitmapDataPlanes: nil, pixelsWide: w, pixelsHigh: h, bitsPerSample: 8, samplesPerPixel: 4, hasAlpha: true, isPlanar: false, colorSpaceName: .deviceRGB, bytesPerRow: 0, bitsPerPixel: 0)!
  let ctx = NSGraphicsContext(bitmapImageRep: rep)!
  NSGraphicsContext.current = ctx
  ctx.cgContext.setFillColor(NSColor.white.cgColor); ctx.cgContext.fill(CGRect(x:0,y:0,width:w,height:h))
  ctx.cgContext.scaleBy(x: scale, y: scale)
  page.draw(with: .mediaBox, to: ctx.cgContext)
  try! rep.representation(using: .png, properties: [:])!.write(to: URL(fileURLWithPath: a[4]))
  print("rendered", w, h)
}
