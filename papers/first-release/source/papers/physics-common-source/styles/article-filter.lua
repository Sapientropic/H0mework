-- Layout-only transformations. Mathematical source is passed through intact.
local function latex_escape(s)
  local map = {['\\']='\\textbackslash{}', ['{']='\\{', ['}']='\\}', ['#']='\\#',
    ['$']='\\$', ['%']='\\%', ['&']='\\&', ['_']='\\_', ['~']='\\textasciitilde{}', ['^']='\\textasciicircum{}'}
  return (s:gsub('[\\{}#$%%&_~^]', map))
end

function Code(el)
  if FORMAT:match('latex') then
    -- \seqsplit drops spaces and may break anywhere, so keep ordinary words
    -- whole and let only long tokens (hashes, paths) break between characters;
    -- words are rejoined with breakable interword spaces.
    local words = {}
    for word in el.text:gmatch('%S+') do
      if #word > 18 then
        table.insert(words, '\\seqsplit{' .. latex_escape(word) .. '}')
      else
        table.insert(words, latex_escape(word))
      end
    end
    return pandoc.RawInline('latex', '\\paperinlinecode{' .. table.concat(words, '\\ ') .. '}')
  end
end

function CodeBlock(el)
  if el.classes:includes('mermaid') then
    return {} -- Original design syntax is not printable art.
  end
end

function Image(el)
  if FORMAT:match('latex') then
    if el.src:match('%.png$') then
      local p = el.src:gsub('%.png$', '-r10.pdf')
      local f = io.open(p, 'rb')
      if f then f:close(); el.src = p end
    elseif el.src:match('%.svg$') then
      local p = el.src:gsub('%.svg$', '.pdf')
      local f = io.open(p, 'rb')
      if f then f:close(); el.src = p end
    end
    el.attributes.width = nil
    el.attributes.height = nil
  end
  return el
end

function Figure(el)
  if not FORMAT:match('latex') then return nil end
  local content = pandoc.Pandoc(el.content):walk({Image = function(img)
    return pandoc.RawInline('latex', '\\includegraphics[width=\\linewidth,height=0.62\\textheight,keepaspectratio]{'
       .. img.src .. '}')
  end})
  local body = pandoc.write(content, 'latex')
  local cap = ''
  if el.caption and el.caption.long and #el.caption.long > 0 then
    cap = pandoc.write(pandoc.Pandoc(el.caption.long), 'latex')
  end
  -- A whole plate and its caption stay at the point of discussion. In
  -- particular, the two adjacent §7 plates cannot share an overflowing float page.
  return pandoc.RawBlock('latex', '\\begin{figure}[H]\n\\centering\n' .. body .. '\n'
    .. (#cap > 0 and ('\\caption*{' .. cap .. '}\n') or '') .. '\\end{figure}')
end

local function merge_figure_caption(blocks)
  local result = pandoc.List()
  local i = 1
  while i <= #blocks do
    local block = blocks[i]
    local following = blocks[i + 1]
    if block.t == 'Figure' and following and following.t == 'Para' then
      local caption_text = pandoc.utils.stringify(following)
      if caption_text:match('^图%s*%d') or caption_text:match('^Figure%s*%d') then
        -- The explanatory caption already carries the figure number and title.
        -- Preserve the image's alt text in Markdown, but do not print it twice.
        block.caption.long = pandoc.Blocks{following}
        result:insert(block)
        i = i + 2
      else
        result:insert(block)
        i = i + 1
      end
    else
      result:insert(block)
      i = i + 1
    end
  end
  return result
end

local function keep_table_intro(blocks)
  local result = pandoc.List()
  for i, block in ipairs(blocks) do
    local next_block = blocks[i+1]
    if block.t == 'Para' and next_block then
      local text = pandoc.utils.stringify(block)
      local table_block = blocks[i+2]
      if next_block.t == 'Para' and table_block and table_block.t == 'Table'
        and text:match('^[A-D]%.%d+%s') then
        -- Appendix table sections need room for their heading and plate; seven
        -- lines alone left the constants table's last row on a separate page.
        result:insert(pandoc.RawBlock('latex', '\\Needspace{0.6\\textheight}'))
      elseif next_block.t == 'Table' then
        result:insert(pandoc.RawBlock('latex', '\\Needspace{7\\baselineskip}'))
      elseif next_block.t == 'OrderedList' or next_block.t == 'BulletList' then
        if text:match('^定理') or text:match('^定义') or text:match('^命题')
          or text:match('^Theorem') or text:match('^Definition') or text:match('^Proposition') then
          result:insert(pandoc.RawBlock('latex', '\\Needspace{8\\baselineskip}'))
        end
      end
    end
    result:insert(block)
  end
  return result
end

return {
  {Code=Code, CodeBlock=CodeBlock, Image=Image},
  {Blocks=merge_figure_caption},
  {Blocks=keep_table_intro},
  {Figure=Figure}
}
